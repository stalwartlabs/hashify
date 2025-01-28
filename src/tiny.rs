/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use std::collections::{BTreeMap, HashMap, HashSet};

use proc_macro::TokenStream;
use quote::quote;
use syn::Expr;

use crate::Key;

#[derive(Debug, Clone)]
pub(crate) enum Algorithm {
    Position { idx: usize },
    Xor { idx1: usize, idx2: usize },
}

#[derive(Clone)]
pub(crate) struct Table<'x> {
    pub algorithm: Algorithm,
    pub positions: Vec<(u8, &'x Key, Value<'x>)>,
    pub default: Value<'x>,
    pub ignore_case: bool,
}

#[derive(Clone)]
pub(crate) enum Value<'x> {
    Some(&'x Expr),
    None,
    True,
    False,
    Expr(&'x Expr),
    Table(Box<Table<'x>>),
}

pub fn build_tiny_map(
    name: Expr,
    options: HashMap<&Key, Value>,
    default: Value,
    ignore_case: bool,
) -> TokenStream {
    let mut map: BTreeMap<usize, HashMap<&Key, Value>> = BTreeMap::new();
    let mut min_key_size = usize::MAX;
    let mut max_key_size = 0;

    for (key, value) in &options {
        let key_size = key.len();
        min_key_size = min_key_size.min(key_size);
        max_key_size = max_key_size.max(key_size);
        map.entry(key_size).or_default().insert(key, value.clone());
    }

    let (header, footer) = if matches!(default, Value::Expr(_)) {
        (
            quote! {
                let __key = #name;
                let mut __matched = true;
            },
            quote! {
                if !__matched {
                    #default
                }
            },
        )
    } else {
        (
            quote! {
                let __key = #name;
            },
            quote! {},
        )
    };

    // Try building a simple lookup table
    if let Some(table) = try_hash(&options, &default, min_key_size, false, ignore_case) {
        let else_cond = if !matches!(default, Value::Expr(_)) {
            quote! {
                else {
                    #default
                }
            }
        } else {
            quote! {
                #footer
            }
        };

        TokenStream::from(quote! {{
            #header

           if (#min_key_size..=#max_key_size).contains(&__key.len()) {
               #table
           } #else_cond
        }})
    } else {
        let match_default = if matches!(default, Value::Expr(_)) {
            quote! {
                 { __matched = false; }
            }
        } else {
            quote! {
                #default
            }
        };

        let match_arms = map.iter().map(|(size, keys)| {
            if keys.len() == 1 {
                let (key, value) = keys.iter().next().unwrap();
                if ignore_case {
                    quote! { #size if __key.eq_ignore_ascii_case(#key) => #value, }
                } else {
                    quote! { #size if __key == #key => #value, }
                }
            } else {
                let table =
                    try_hash(keys, &default, *size, true, ignore_case).unwrap_or_else(|| {
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
           #header

           match __key.len() {
               #(#match_arms)*
               _ => #match_default,
           }

           #footer
        }})
    }
}

impl Algorithm {
    pub fn hash(&self, value: &[u8]) -> u8 {
        match self {
            Algorithm::Position { idx } => value[*idx],
            Algorithm::Xor { idx1, idx2 } => value[*idx1] ^ value[*idx2],
        }
    }
}

pub(crate) fn try_hash<'x>(
    keys: &HashMap<&'x Key, Value<'x>>,
    default: &Value<'x>,
    size: usize,
    is_final_pass: bool,
    ignore_case: bool,
) -> Option<Table<'x>> {
    // Use direct mapping
    if size == 1 && is_final_pass {
        return Some(Table {
            algorithm: Algorithm::Position { idx: 0 },
            positions: keys
                .iter()
                .collect::<BTreeMap<_, _>>()
                .iter()
                .map(|(key, value)| (key.as_bytes()[0], **key, (*value).clone()))
                .collect(),
            ignore_case,
            default: default.clone(),
        });
    }

    // Try finding a key index that contains a byte unique to all keys
    let mut best_match_count = 0;
    let mut best_match_algo = Algorithm::Position { idx: 0 };
    for idx in 0..size {
        let mut byte_set = HashSet::new();
        let algorithm = Algorithm::Position { idx };
        for key in keys.keys() {
            byte_set.insert(algorithm.hash(key.as_bytes()));
        }
        if byte_set.len() == keys.len() {
            return Some(Table {
                positions: keys
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .iter()
                    .map(|(key, value)| (algorithm.hash(key.as_bytes()), **key, (*value).clone()))
                    .collect(),
                algorithm,
                ignore_case,
                default: default.clone(),
            });
        } else if byte_set.len() > best_match_count {
            best_match_count = byte_set.len();
            best_match_algo = Algorithm::Position { idx };
        }
    }

    // Try XORing key positions
    for i in 0..size {
        for j in i + 1..size {
            let mut byte_set = HashSet::new();
            let algorithm = Algorithm::Xor { idx1: i, idx2: j };
            for key in keys.keys() {
                byte_set.insert(algorithm.hash(key.as_bytes()));
            }
            if byte_set.len() == keys.len() {
                return Some(Table {
                    positions: keys
                        .iter()
                        .map(|(key, value)| (algorithm.hash(key.as_bytes()), (*key, value.clone())))
                        .collect::<BTreeMap<_, _>>()
                        .into_iter()
                        .map(|(key, (a, b))| (key, a, b))
                        .collect(),
                    algorithm,
                    ignore_case,
                    default: default.clone(),
                });
            } else if byte_set.len() > best_match_count {
                best_match_count = byte_set.len();
                best_match_algo = algorithm;
            }
        }
    }

    if is_final_pass {
        let mut key_groups = HashMap::new();
        for (key, value) in keys {
            key_groups
                .entry(best_match_algo.hash(key.as_bytes()))
                .or_insert_with(HashMap::new)
                .insert(*key, value.clone());
        }
        let mut table = Table {
            algorithm: best_match_algo,
            positions: Vec::with_capacity(keys.len()),
            default: default.clone(),
            ignore_case,
        };

        for (hash, keys) in key_groups {
            if keys.len() > 1 {
                let sub_table = try_hash(&keys, default, size, true, ignore_case).unwrap();
                table.positions.push((
                    hash,
                    keys.keys().next().unwrap(),
                    Value::Table(Box::new(sub_table)),
                ));
            } else {
                let (key, value) = keys.into_iter().next().unwrap();
                table.positions.push((hash, key, value));
            }
        }

        Some(table)
    } else {
        None
    }
}

impl quote::ToTokens for Table<'_> {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let algorithm = match &self.algorithm {
            Algorithm::Position { idx } => {
                if self.ignore_case {
                    quote! { let hash = __key[#idx].to_ascii_lowercase(); }
                } else {
                    quote! { let hash = __key[#idx]; }
                }
            }
            Algorithm::Xor { idx1, idx2 } => {
                if self.ignore_case {
                    quote! { let hash = __key[#idx1].to_ascii_lowercase() ^ __key[#idx2].to_ascii_lowercase(); }
                } else {
                    quote! { let hash = __key[#idx1] ^ __key[#idx2]; }
                }
            }
        };

        let match_default = if matches!(self.default, Value::Expr(_)) {
            quote! {
                 { __matched = false; }
            }
        } else {
            let default = &self.default;
            quote! {
                #default
            }
        };
        let match_arms = self.positions.iter().map(|(hash, key, value)| {
            if key.len() > 1 && !matches!(value, Value::Table(_)) {
                if self.ignore_case {
                    quote! { #hash if __key.eq_ignore_ascii_case(#key) => #value, }
                } else {
                    quote! { #hash if __key == #key => #value, }
                }
            } else {
                quote! { #hash => #value, }
            }
        });

        tokens.extend(quote! {
            #algorithm
            match hash {
                #(#match_arms)*
                _ => #match_default,
            }
        });
    }
}

impl quote::ToTokens for Value<'_> {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.extend(match self {
            Value::Some(expr) => quote! { Some(#expr) },
            Value::None => quote! { None },
            Value::True => quote! { true },
            Value::False => quote! { false },
            Value::Expr(expr) => quote! { #expr },
            Value::Table(table) => quote! {{ #table }},
        });
    }
}
