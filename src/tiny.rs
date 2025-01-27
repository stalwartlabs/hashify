/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use std::collections::{BTreeMap, HashMap, HashSet};

use proc_macro::TokenStream;
use quote::quote;
use syn::Expr;

#[derive(Debug)]
pub(crate) enum Algorithm {
    Position { idx: usize },
    Xor { idx1: usize, idx2: usize },
    Fnv { shift: Option<usize> },
    Djb2 { shift: Option<usize> },
    Sdbm { shift: Option<usize> },
    Jenkins { shift: Option<usize> },
    Murmur2 { shift: Option<usize> },
}

pub(crate) struct Table<'x> {
    pub algorithm: Algorithm,
    pub positions: Vec<(HashValue, &'x str, Option<&'x Expr>)>,
    pub ignore_case: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum HashValue {
    U8(u8),
    U16(u16),
}

pub fn build_tiny_map(
    name: Expr,
    options: HashMap<String, Option<&Expr>>,
    ignore_case: bool,
) -> TokenStream {
    let mut map: BTreeMap<usize, HashMap<String, Option<&Expr>>> = BTreeMap::new();
    let mut min_key_size = usize::MAX;
    let mut max_key_size = 0;

    let mut is_map = false;
    for (key, value) in &options {
        let key_size = key.len();
        min_key_size = min_key_size.min(key_size);
        max_key_size = max_key_size.max(key_size);
        is_map = value.is_some();
        map.entry(key_size)
            .or_default()
            .insert(key.to_string(), *value);
    }

    let default_value = if is_map {
        quote! { None }
    } else {
        quote! { false }
    };

    // Try building a simple lookup table
    if let Some(table) = try_hash(&options, min_key_size, false, ignore_case) {
        TokenStream::from(quote! {{
           let key = #name;
           if key.len() >= #min_key_size && key.len() <= #max_key_size {
               #table
           } else {
               #default_value
           }
        }})
    } else {
        let match_arms = map.iter().map(|(size, keys)| {
            if keys.len() == 1 {
                let (key, value) = keys.iter().next().unwrap();
                let return_value = match value {
                    Some(value) => {
                        quote! { Some(#value) }
                    }
                    None => quote! { true },
                };
                if ignore_case {
                    quote! { #size if key.eq_ignore_ascii_case(#key.as_bytes()) => #return_value, }
                } else {
                    quote! { #size if key == #key.as_bytes() => #return_value, }
                }
            } else {
                let table = try_hash(keys, *size, true, ignore_case).unwrap_or_else(|| {
                    panic!(
                        "Failed to build lookup table for {} keys: {:?}",
                        keys.len(),
                        keys.iter().map(|(k, _)| k).collect::<Vec<_>>()
                    )
                });
                quote! { #size => { #table } }
            }
        });

        TokenStream::from(quote! {{
           let key = #name;
           match key.len() {
               #(#match_arms)*
               _ => #default_value,
           }
        }})
    }
}

impl Algorithm {
    pub fn hash(&self, value: &[u8]) -> u64 {
        match self {
            Algorithm::Position { idx } => value[*idx] as u64,
            Algorithm::Xor { idx1, idx2 } => value[*idx1] as u64 ^ value[*idx2] as u64,
            Algorithm::Fnv { shift } => {
                value.iter().fold(0x811c_9dc5u64, |hash, byte| {
                    hash.wrapping_mul(0x0100_0000_01b3u64)
                        .wrapping_add(*byte as u64)
                }) & shift.map_or(u64::MAX, |s| (1 << s) - 1)
            }
            Algorithm::Djb2 { shift } => {
                value
                    .iter()
                    .fold(5381u64, |h, &c| h.wrapping_mul(33).wrapping_add(c as u64))
                    & shift.map_or(u64::MAX, |s| (1 << s) - 1)
            }
            Algorithm::Sdbm { shift } => {
                value.iter().fold(0u64, |h, &c| {
                    (c as u64)
                        .wrapping_add(h << 6)
                        .wrapping_add(h << 16)
                        .wrapping_sub(h)
                }) & shift.map_or(u64::MAX, |s| (1 << s) - 1)
            }
            Algorithm::Jenkins { shift } => {
                value.iter().fold(0u64, |h, &c| {
                    h.wrapping_add(c as u64)
                        .rotate_left(10)
                        .wrapping_mul(0x7FEB352D)
                }) & shift.map_or(u64::MAX, |s| (1 << s) - 1)
            }
            Algorithm::Murmur2 { shift } => {
                value.iter().fold(0u64, |h, &c| {
                    (h.wrapping_mul(0x5bd1e995).rotate_left(24) ^ (c as u64))
                        .wrapping_mul(0x5bd1e995)
                }) & shift.map_or(u64::MAX, |s| (1 << s) - 1)
            }
        }
    }
}

pub(crate) fn try_hash<'x>(
    keys: &'x HashMap<String, Option<&'x Expr>>,
    size: usize,
    with_fallback: bool,
    ignore_case: bool,
) -> Option<Table<'x>> {
    // Use direct mapping
    if size == 1 && with_fallback {
        return Some(Table {
            algorithm: Algorithm::Position { idx: 0 },
            positions: keys
                .iter()
                .collect::<BTreeMap<_, _>>()
                .iter()
                .map(|(key, value)| (key.as_bytes()[0].into(), key.as_str(), **value))
                .collect(),
            ignore_case,
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
                positions: keys
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .iter()
                    .map(|(key, value)| (key.as_bytes()[idx].into(), key.as_str(), **value))
                    .collect(),
                ignore_case,
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
                    positions: keys
                        .iter()
                        .map(|(key, value)| {
                            (
                                HashValue::U8(key.as_bytes()[i] ^ key.as_bytes()[j]),
                                (key.as_str(), *value),
                            )
                        })
                        .collect::<BTreeMap<_, _>>()
                        .into_iter()
                        .map(|(key, (a, b))| (key, a, b))
                        .collect(),
                    ignore_case,
                });
            }
        }
    }

    // Try FNV-1a hash
    if size <= u8::MAX as usize {
        for algorithm in [
            Algorithm::Fnv { shift: None },
            Algorithm::Djb2 { shift: None },
            Algorithm::Sdbm { shift: None },
            Algorithm::Jenkins { shift: None },
            Algorithm::Murmur2 { shift: None },
        ] {
            let mut byte_set = HashSet::new();
            for key in keys.keys() {
                byte_set.insert(algorithm.hash(key.as_bytes()) as u8);
            }
            if byte_set.len() == keys.len() {
                return Some(Table {
                    positions: keys
                        .iter()
                        .map(|(key, value)| {
                            (
                                HashValue::U8(algorithm.hash(key.as_bytes()) as u8),
                                (key.as_str(), *value),
                            )
                        })
                        .collect::<BTreeMap<_, _>>()
                        .into_iter()
                        .map(|(key, (a, b))| (key, a, b))
                        .collect(),
                    algorithm,
                    ignore_case,
                });
            }
        }
    }

    // Fallback to larger hash values
    if with_fallback && size <= u16::MAX as usize {
        for shift in 9..=16 {
            for algorithm in [
                Algorithm::Fnv { shift: Some(shift) },
                Algorithm::Djb2 { shift: Some(shift) },
                Algorithm::Sdbm { shift: Some(shift) },
                Algorithm::Jenkins { shift: Some(shift) },
                Algorithm::Murmur2 { shift: Some(shift) },
            ] {
                let mut byte_set = HashSet::new();
                for key in keys.keys() {
                    byte_set.insert(algorithm.hash(key.as_bytes()));
                }
                if byte_set.len() == keys.len() {
                    return Some(Table {
                        positions: keys
                            .iter()
                            .map(|(key, value)| {
                                (
                                    HashValue::U16(algorithm.hash(key.as_bytes()) as u16),
                                    (key.as_str(), *value),
                                )
                            })
                            .collect::<BTreeMap<_, _>>()
                            .into_iter()
                            .map(|(key, (a, b))| (key, a, b))
                            .collect(),
                        algorithm,
                        ignore_case,
                    });
                }
            }
        }
    }

    None
}

impl quote::ToTokens for Table<'_> {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let c = if self.ignore_case {
            quote! { c.to_ascii_lowercase() }
        } else {
            quote! { c }
        };

        let algorithm = match &self.algorithm {
            Algorithm::Position { idx } => {
                if self.ignore_case {
                    quote! { let hash = key[#idx].to_ascii_lowercase(); }
                } else {
                    quote! { let hash = key[#idx]; }
                }
            }
            Algorithm::Xor { idx1, idx2 } => {
                if self.ignore_case {
                    quote! { let hash = key[#idx1].to_ascii_lowercase() ^ key[#idx2].to_ascii_lowercase(); }
                } else {
                    quote! { let hash = key[#idx1] ^ key[#idx2]; }
                }
            }
            Algorithm::Fnv { shift } => {
                let (shift, cast) = match shift {
                    Some(shift) => (quote! { & ((1 << #shift) - 1) }, quote! { u16 }),
                    None => (quote! {}, quote! { u8 }),
                };

                quote! {
                    let hash = (key.iter().fold(0x811c_9dc5u64, |h, &c| {
                        h.wrapping_mul(0x0100_0000_01b3).wrapping_add(#c as u64)
                    }) #shift) as #cast;
                }
            }
            Algorithm::Djb2 { shift } => {
                let (shift, cast) = match shift {
                    Some(shift) => (quote! { & ((1 << #shift) - 1) }, quote! { u16 }),
                    None => (quote! {}, quote! { u8 }),
                };

                quote! {
                    let hash = (key.iter().fold(5381u64, |h, &c| h.wrapping_mul(33).wrapping_add(#c as u64)) #shift) as #cast;
                }
            }
            Algorithm::Sdbm { shift } => {
                let (shift, cast) = match shift {
                    Some(shift) => (quote! { & ((1 << #shift) - 1) }, quote! { u16 }),
                    None => (quote! {}, quote! { u8 }),
                };

                quote! {
                    let hash = (key.iter().fold(0u64, |h, &c| (#c as u64)
                    .wrapping_add(h << 6)
                    .wrapping_add(h << 16)
                    .wrapping_sub(h)) #shift) as #cast;
                }
            }
            Algorithm::Jenkins { shift } => {
                let (shift, cast) = match shift {
                    Some(shift) => (quote! { & ((1 << #shift) - 1) }, quote! { u16 }),
                    None => (quote! {}, quote! { u8 }),
                };

                quote! {
                    let hash = (key.iter().fold(0u64, |h, &c| {
                        h.wrapping_add(#c as u64)
                            .rotate_left(10)
                            .wrapping_mul(0x7FEB352D)
                    })  #shift) as #cast;
                }
            }
            Algorithm::Murmur2 { shift } => {
                let (shift, cast) = match shift {
                    Some(shift) => (quote! { & ((1 << #shift) - 1) }, quote! { u16 }),
                    None => (quote! {}, quote! { u8 }),
                };

                quote! {
                    let hash = (key.iter().fold(0u64, |h, &c| {
                        (h.wrapping_mul(0x5bd1e995).rotate_left(24) ^ (#c as u64)).wrapping_mul(0x5bd1e995)
                    })  #shift) as #cast;
                }
            }
        };

        let match_arms = self.positions.iter().map(|(hash, key, value)| {
            let return_value = match value {
                Some(value) => {
                    quote! { Some(#value) }
                }
                None => quote! { true },
            };

            if key.len() > 1 {
                if self.ignore_case {
                    quote! { #hash if key.eq_ignore_ascii_case(#key.as_bytes()) => #return_value, }
                } else {
                    quote! { #hash if key == #key.as_bytes() => #return_value, }
                }
            } else {
                quote! { #hash => #return_value, }
            }
        });

        let default_value = if self.positions.iter().any(|(_, _, value)| value.is_some()) {
            quote! { None }
        } else {
            quote! { false }
        };

        tokens.extend(quote! {
            #algorithm
            match hash {
                #(#match_arms)*
                _ => #default_value,
            }
        });
    }
}

impl quote::ToTokens for HashValue {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            HashValue::U8(value) => tokens.extend(quote! { #value }),
            HashValue::U16(value) => tokens.extend(quote! { #value }),
        }
    }
}

impl From<u8> for HashValue {
    fn from(value: u8) -> Self {
        HashValue::U8(value)
    }
}
