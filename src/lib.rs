#![doc = include_str!("../README.md")]
/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use std::collections::{BTreeMap, HashMap, HashSet};

use proc_macro::TokenStream;
use quote::quote;
use syn::punctuated::Punctuated;
use syn::LitStr;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, Expr, Result, Token,
};

struct MapInput {
    name: Expr,
    pairs: Punctuated<KeyValue, Token![,]>,
}

struct SetInput {
    name: Expr,
    pairs: Punctuated<Key, Token![,]>,
}

impl Parse for MapInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let pairs = input.parse_terminated(KeyValue::parse, Token![,])?;
        Ok(MapInput { name, pairs })
    }
}

impl Parse for SetInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let pairs = input.parse_terminated(Key::parse, Token![,])?;
        Ok(SetInput { name, pairs })
    }
}

struct KeyValue {
    key: LitStr,
    value: Expr,
}

impl Parse for KeyValue {
    fn parse(input: ParseStream) -> Result<Self> {
        let key: LitStr = input.parse()?;
        input.parse::<Token![=>]>()?;
        let value: Expr = input.parse()?;
        Ok(KeyValue { key, value })
    }
}

struct Key {
    key: LitStr,
}

impl Parse for Key {
    fn parse(input: ParseStream) -> Result<Self> {
        let key: LitStr = input.parse()?;
        Ok(Key { key })
    }
}

enum Algorithm {
    Position { idx: usize },
    Xor { idx1: usize, idx2: usize },
    Fnv { seed: u64 },
}

struct Table<'x> {
    pub algorithm: Algorithm,
    pub is_map: bool,
    pub positions: Vec<(u8, &'x str, &'x Expr)>,
}

struct KeySizeMap<'x> {
    map: BTreeMap<usize, HashMap<String, &'x Expr>>,
    min_key_size: usize,
    max_key_size: usize,
}

impl<'x> KeySizeMap<'x> {
    fn build(options: &'x HashMap<String, &'x Expr>) -> Self {
        let mut map: BTreeMap<usize, HashMap<String, &Expr>> = BTreeMap::new();
        let mut min_key_size = usize::MAX;
        let mut max_key_size = 0;

        for (key, value) in options {
            let key_size = key.len();
            min_key_size = min_key_size.min(key_size);
            max_key_size = max_key_size.max(key_size);
            map.entry(key_size)
                .or_default()
                .insert(key.to_string(), value);
        }

        KeySizeMap {
            map,
            min_key_size,
            max_key_size,
        }
    }
}

#[proc_macro]
pub fn map(input: TokenStream) -> TokenStream {
    let MapInput { name, pairs } = parse_macro_input!(input);

    let options = pairs
        .iter()
        .map(|kv| (kv.key.value(), &kv.value))
        .collect::<HashMap<_, _>>();

    let size_map = KeySizeMap::build(&options);

    // Try building a simple lookup table
    if let Some(table) = try_hash(&options, size_map.min_key_size) {
        let min = size_map.min_key_size;
        let max = size_map.max_key_size;

        TokenStream::from(quote! {
           {let key = #name;
           if key.len() >= #min && key.len() <= #max {
               #table
           } else {
               None
           }}
        })
    } else {
        let match_arms = size_map.map.iter().map(|(size, keys)| {
            if keys.len() == 1 {
                let (key, value) = keys.iter().next().unwrap();
                quote! { #size if key == #key.as_bytes() => Some(#value), }
            } else {
                let table = try_hash(keys, *size).expect("Failed to build lookup table for keys");
                quote! { #size => { #table } }
            }
        });

        TokenStream::from(quote! {{
           let key = #name;
           match key.len() {
               #(#match_arms)*
               _ => None,
           }
        }})
    }
}

#[proc_macro]
pub fn set(input: TokenStream) -> TokenStream {
    let SetInput { name, pairs } = parse_macro_input!(input);
    let true_ = syn::Expr::Lit(syn::ExprLit {
        attrs: vec![],
        lit: syn::Lit::Bool(syn::LitBool {
            value: true,
            span: proc_macro2::Span::call_site(),
        }),
    });

    let options = pairs
        .iter()
        .map(|kv| (kv.key.value(), &true_))
        .collect::<HashMap<_, _>>();

    let size_map = KeySizeMap::build(&options);

    // Try building a simple lookup table
    if let Some(mut table) = try_hash(&options, size_map.min_key_size) {
        table.is_map = false;
        let min = size_map.min_key_size;
        let max = size_map.max_key_size;

        TokenStream::from(quote! {{
           let key = #name;
           if key.len() >= #min && key.len() <= #max {
               #table
           } else {
               false
           }
        }})
    } else {
        let match_arms = size_map.map.iter().map(|(size, keys)| {
            if keys.len() == 1 {
                let (key, _) = keys.iter().next().unwrap();
                quote! { #size if key == #key.as_bytes() => true, }
            } else {
                let mut table =
                    try_hash(keys, *size).expect("Failed to build lookup table for keys");
                table.is_map = false;
                quote! { #size => { #table } }
            }
        });

        TokenStream::from(quote! {{
           let key = #name;
           match key.len() {
               #(#match_arms)*
               _ => false,
           }
        }})
    }
}

fn try_hash<'x>(keys: &'x HashMap<String, &'x Expr>, size: usize) -> Option<Table<'x>> {
    // Use direct mapping
    if size == 1 {
        return Some(Table {
            algorithm: Algorithm::Position { idx: 0 },
            is_map: true,
            positions: keys
                .iter()
                .collect::<BTreeMap<_, _>>()
                .iter()
                .map(|(key, value)| (key.as_bytes()[0], key.as_str(), **value))
                .collect(),
        });
    }

    // Try finding a key index that contains a byte unique to all keys
    for idx in 0..size {
        let mut byte_set = HashSet::new();
        for key in keys.keys() {
            byte_set.insert(key.as_bytes()[idx]);
        }
        if byte_set.len() == keys.len() {
            return Some(Table {
                algorithm: Algorithm::Position { idx },
                is_map: true,
                positions: keys
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .iter()
                    .map(|(key, value)| (key.as_bytes()[idx], key.as_str(), **value))
                    .collect(),
            });
        }
    }

    // Try XORing key positions
    for i in 0..size {
        for j in i + 1..size {
            let mut byte_set = HashSet::new();
            for key in keys.keys() {
                byte_set.insert(key.as_bytes()[i] ^ key.as_bytes()[j]);
            }
            if byte_set.len() == keys.len() {
                return Some(Table {
                    algorithm: Algorithm::Xor { idx1: i, idx2: j },
                    is_map: true,
                    positions: keys
                        .iter()
                        .map(|(key, value)| {
                            (
                                key.as_bytes()[i] ^ key.as_bytes()[j],
                                (key.as_str(), *value),
                            )
                        })
                        .collect::<BTreeMap<_, _>>()
                        .into_iter()
                        .map(|(key, (a, b))| (key, a, b))
                        .collect(),
                });
            }
        }
    }

    // Try FNV-1a hash
    for seed in [
        0x811c_9dc5u64,
        0x01000193u64,
        0xcbf29ce484222325u64,
        0x8422_2225u64,
    ] {
        let mut byte_set = HashSet::new();
        for key in keys.keys() {
            byte_set.insert(key.as_bytes().iter().fold(seed, |hash, byte| {
                hash.wrapping_mul(0x0100_0000_01b3)
                    .wrapping_add(*byte as u64)
            }) as u8);
        }
        if byte_set.len() == keys.len() {
            return Some(Table {
                algorithm: Algorithm::Fnv { seed },
                is_map: true,
                positions: keys
                    .iter()
                    .map(|(key, value)| {
                        (
                            key.as_bytes().iter().fold(seed, |hash, byte| {
                                hash.wrapping_mul(0x0100_0000_01b3)
                                    .wrapping_add(*byte as u64)
                            }) as u8,
                            (key.as_str(), *value),
                        )
                    })
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(key, (a, b))| (key, a, b))
                    .collect(),
            });
        }
    }

    None
}

impl quote::ToTokens for Table<'_> {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let algorithm = match &self.algorithm {
            Algorithm::Position { idx } => {
                quote! { let hash = key[#idx]; }
            }
            Algorithm::Xor { idx1, idx2 } => {
                quote! { let hash = key[#idx1] ^ key[#idx2]; }
            }
            Algorithm::Fnv { seed } => {
                quote! {
                    let hash = key.iter().fold(#seed, |h, b| {
                        h.wrapping_mul(0x0100_0000_01b3).wrapping_add(*b as u64)
                    }) as u8;
                }
            }
        };

        if self.is_map {
            let match_arms = self.positions.iter().map(|(hash, key, value)| {
                if key.len() > 1 {
                    quote! { #hash if key == #key.as_bytes() => Some(#value), }
                } else {
                    quote! { #hash => Some(#value), }
                }
            });

            tokens.extend(quote! {
                #algorithm
                match hash {
                    #(#match_arms)*
                    _ => None,
                }
            });
        } else {
            let match_arms = self.positions.iter().map(|(hash, key, _)| {
                if key.len() > 1 {
                    quote! { #hash if key == #key.as_bytes() => true, }
                } else {
                    quote! { #hash => true, }
                }
            });

            tokens.extend(quote! {
                #algorithm
                match hash {
                    #(#match_arms)*
                    _ => false,
                }
            });
        }
    }
}
