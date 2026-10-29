/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

macro_rules! code {
    ($($tokens:tt)*) => {
        ::quote::quote_spanned!(::proc_macro2::Span::mixed_site() => $($tokens)*)
    };
}

mod builder;
mod hasher;
mod switch;

use builder::Mphf;
use hasher::{HashWord, SHORT_KEY_MAX_LEN, Words};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::ToTokens;
use switch::{Leaves, Switch};
use syn::{Expr, LitByteStr, Stmt, Type};

const SWITCH_MAX_KEYS: usize = 3;
const FLAT_MAX_KEYS: usize = 64;
const INLINE_DEFAULT_MAX_TOKENS: usize = 16;

pub(crate) enum Payload<'x> {
    Value {
        ty: &'x Type,
        values: Vec<&'x Expr>,
    },
    Presence,
    Arms {
        arms: Vec<&'x Expr>,
        default: &'x Expr,
    },
}

pub(crate) struct Lookup<'x> {
    keys: Vec<&'x [u8]>,
    payload: Payload<'x>,
    ignore_case: bool,
}

struct Table<H> {
    entries: Vec<usize>,
    min_len: usize,
    max_len: usize,
    mphf: Mphf<H>,
}

impl<'x> Lookup<'x> {
    pub(crate) fn new(
        keys: Vec<&'x [u8]>,
        payload: Payload<'x>,
        ignore_case: bool,
    ) -> Result<Self, TokenStream> {
        let mut sorted = keys.clone();
        sorted.sort_unstable();
        if let Some(pair) = sorted.windows(2).find(|pair| pair[0] == pair[1]) {
            let message = format!("duplicate key {:?}", String::from_utf8_lossy(pair[0]));
            return Err(code! { ::core::compile_error!(#message) });
        }
        Ok(Lookup {
            keys,
            payload,
            ignore_case,
        })
    }

    pub(crate) fn expand(&self, name: &Expr) -> TokenStream {
        if self.keys.len() <= SWITCH_MAX_KEYS {
            return self.switch(name);
        }

        let lookup = match (self.lookup::<u32>(name), self.lookup::<u64>(name)) {
            (Some(lookup_32), Some(lookup_64)) => code! {{
                #[cfg(target_pointer_width = "64")]
                let __value = #lookup_64;
                #[cfg(not(target_pointer_width = "64"))]
                let __value = #lookup_32;
                __value
            }},
            (Some(lookup), None) | (None, Some(lookup)) => lookup,
            (None, None) => {
                return code! { ::core::compile_error!("failed to resolve hash collision") };
            }
        };
        self.dispatch(lookup)
    }

    fn key(name: &Expr) -> TokenStream {
        code! {
            let __key = #name;
            let __key: &[::core::primitive::u8] = &__key[..];
            let __len = __key.len();
        }
    }

    fn switch(&self, name: &Expr) -> TokenStream {
        let switch = Switch::new(&self.keys, self.ignore_case);
        let key = Self::key(name);
        let missing = self.not_found();
        match &self.payload {
            Payload::Value { ty, values } => {
                let len = values.len();
                let body = switch.tokens(&Leaves {
                    found: &|idx| code! { ::core::option::Option::Some(&__VALUES[#idx]) },
                    missing,
                });
                code! {{
                    static __VALUES: [#ty; #len] = [#(#values),*];
                    #key
                    #body
                }}
            }
            Payload::Presence => {
                let body = switch.tokens(&Leaves {
                    found: &|_| code! { true },
                    missing,
                });
                code! {{ #key #body }}
            }
            Payload::Arms { arms, default } if Self::inline_arms(arms, default) => {
                let body = switch.tokens(&Leaves {
                    found: &|idx| arms[idx].to_token_stream(),
                    missing: default.to_token_stream(),
                });
                code! {{ #key #body }}
            }
            Payload::Arms { .. } => {
                let body = switch.tokens(&Leaves {
                    found: &|idx| code! { #idx },
                    missing,
                });
                self.dispatch(code! {{ #key #body }})
            }
        }
    }

    fn inline_arms(arms: &[&Expr], default: &Expr) -> bool {
        !arms.iter().chain([&default]).all(|arm| is_statement(arm))
            && token_count(default.to_token_stream()) <= INLINE_DEFAULT_MAX_TOKENS
    }

    fn dispatch(&self, index: TokenStream) -> TokenStream {
        let Payload::Arms { arms, default } = &self.payload else {
            return index;
        };
        let arms = arms
            .iter()
            .enumerate()
            .map(|(idx, arm)| code! { #idx => #arm, });
        code! {{
            match #index {
                #(#arms)*
                _ => #default,
            }
        }}
    }

    fn lookup<H: HashWord>(&self, name: &Expr) -> Option<TokenStream> {
        let (short, long): (Vec<usize>, Vec<usize>) =
            (0..self.keys.len()).partition(|&idx| self.keys[idx].len() <= SHORT_KEY_MAX_LEN);
        if !(H::fits(short.len()) && H::fits(long.len())) {
            return None;
        }
        let short = self.table::<H, _>(
            short,
            |key| (Words::of(key), key.len()),
            |&(words, len), seeds| H::hash_flat(words, len, seeds),
            |&(words, len), seeds| H::hash_short(words, len, seeds),
        )?;
        let long = self.table::<H, _>(
            long,
            |key| key,
            |key, seeds| H::hash_long(key, seeds),
            |key, seeds| H::hash_long(key, seeds),
        )?;

        let not_found = self.not_found();
        let body = short
            .iter()
            .map(|table| (table, self.short_lookup(table)))
            .chain(long.iter().map(|table| (table, self.long_lookup(table))))
            .rev()
            .fold(code! { { #not_found } }, |otherwise, (table, lookup)| {
                let (min_len, max_len) = (table.min_len, table.max_len);
                code! {
                    if (#min_len..=#max_len).contains(&__len) { #lookup } else #otherwise
                }
            });
        let key = Self::key(name);

        Some(code! {{
            #key
            #body
        }})
    }

    fn table<H: HashWord, K>(
        &self,
        entries: Vec<usize>,
        input: impl Fn(&'x [u8]) -> K,
        flat_hash: impl Fn(&K, &[H; 3]) -> H,
        hash: impl Fn(&K, &[H; 3]) -> H,
    ) -> Option<Option<Table<H>>> {
        if entries.is_empty() {
            return Some(None);
        }
        let inputs: Vec<K> = entries.iter().map(|&idx| input(self.keys[idx])).collect();
        let mphf = (inputs.len() <= FLAT_MAX_KEYS)
            .then(|| builder::build_flat(&inputs, flat_hash))
            .flatten()
            .or_else(|| builder::build(&inputs, hash))?;
        let lens = entries.iter().map(|&idx| self.keys[idx].len());
        let min_len = lens.clone().min().unwrap_or_default();
        let max_len = lens.max().unwrap_or_default();
        Some(Some(Table {
            entries,
            min_len,
            max_len,
            mphf,
        }))
    }

    fn not_found(&self) -> TokenStream {
        match self.payload {
            Payload::Value { .. } => code! { ::core::option::Option::None },
            Payload::Presence => code! { false },
            Payload::Arms { .. } => code! { ::core::primitive::usize::MAX },
        }
    }

    fn found(&self, payload_field: TokenStream) -> TokenStream {
        match self.payload {
            Payload::Value { .. } => {
                code! { ::core::option::Option::Some(&__entry.#payload_field) }
            }
            Payload::Presence => code! { true },
            Payload::Arms { .. } => code! { __entry.#payload_field as ::core::primitive::usize },
        }
    }

    fn payload_row(&self, entry: Option<usize>) -> Option<TokenStream> {
        match &self.payload {
            Payload::Value { values, .. } => Some(match entry {
                Some(entry) => {
                    let value = values[entry];
                    code! { #value }
                }
                None => code! { __FILL },
            }),
            Payload::Presence => None,
            Payload::Arms { .. } => {
                let index = entry.unwrap_or_default() as u32;
                Some(code! { #index })
            }
        }
    }

    fn fill<H>(&self, table: &Table<H>) -> Option<TokenStream> {
        let Payload::Value { ty, values } = &self.payload else {
            return None;
        };
        let value = values[*table.entries.first()?];
        table
            .mphf
            .slots
            .contains(&None)
            .then(|| code! { const __FILL: #ty = #value; })
    }

    fn payload_ty(&self) -> Option<TokenStream> {
        match &self.payload {
            Payload::Value { ty, .. } => Some(code! { #ty }),
            Payload::Presence => None,
            Payload::Arms { .. } => Some(code! { ::core::primitive::u32 }),
        }
    }

    fn locate<H: HashWord>(pilots: &[u8], slots_len: usize) -> TokenStream {
        if pilots.is_empty() {
            let slot = H::top_tokens(slots_len.trailing_zeros());
            code! { let __entry = &__TABLE[#slot]; }
        } else {
            let pilots_len = pilots.len();
            let bucket = H::bucket_tokens(pilots_len);
            let slot = H::slot_tokens(slots_len);
            code! {
                static __PILOTS: [::core::primitive::u8; #pilots_len] = [#(#pilots),*];
                let __pilot = __PILOTS[#bucket];
                let __entry = &__TABLE[#slot];
            }
        }
    }

    fn short_lookup<H: HashWord>(&self, table: &Table<H>) -> TokenStream {
        let Mphf {
            seeds,
            pilots,
            slots,
        } = &table.mphf;
        let hash_ty = H::ty();
        let words = Words::tokens(table.min_len, table.max_len, self.ignore_case);
        let hash = if pilots.is_empty() {
            H::hash_flat_tokens(seeds)
        } else {
            H::hash_short_tokens(seeds)
        };
        let slots_len = slots.len();
        let locate = Self::locate::<H>(pilots, slots_len);

        let rows = slots.iter().map(|&slot| {
            let entry = slot.map(|idx| table.entries[idx]);
            let (Words { a, b }, len) = entry.map_or((Words { a: 0, b: 0 }, u8::MAX), |entry| {
                let key = self.keys[entry];
                (Words::of(key), key.len() as u8)
            });
            match self.payload_row(entry) {
                Some(payload) => code! { (#a, #b, #len, #payload) },
                None => code! { (#a, #b, #len) },
            }
        });
        let row_ty = match self.payload_ty() {
            Some(payload_ty) => code! {
                (
                    ::core::primitive::u64,
                    ::core::primitive::u64,
                    ::core::primitive::u8,
                    #payload_ty,
                )
            },
            None => code! {
                (::core::primitive::u64, ::core::primitive::u64, ::core::primitive::u8)
            },
        };
        let found = self.found(code!(3));
        let not_found = self.not_found();

        let fill = self.fill(table);

        code! {{
            #fill
            static __TABLE: [#row_ty; #slots_len] = [#(#rows),*];
            let __words: (::core::primitive::u64, ::core::primitive::u64) = #words;
            let __hash: #hash_ty = #hash;
            #locate
            if (__entry.0 == __words.0)
                & (__entry.1 == __words.1)
                & (__entry.2 as ::core::primitive::usize == __len)
            {
                #found
            } else {
                #not_found
            }
        }}
    }

    fn long_lookup<H: HashWord>(&self, table: &Table<H>) -> TokenStream {
        let Mphf {
            seeds,
            pilots,
            slots,
        } = &table.mphf;
        let hash_ty = H::ty();
        let hash = H::hash_long_tokens(seeds, self.ignore_case);
        let slots_len = slots.len();
        let locate = Self::locate::<H>(pilots, slots_len);

        let rows = slots.iter().map(|&slot| {
            let entry = slot.map(|idx| table.entries[idx]);
            let key = LitByteStr::new(
                entry.map_or(&[][..], |entry| self.keys[entry]),
                Span::mixed_site(),
            );
            match self.payload_row(entry) {
                Some(payload) => code! { (#key, #payload) },
                None => code! { (#key,) },
            }
        });
        let row_ty = match self.payload_ty() {
            Some(payload_ty) => code! { (&[::core::primitive::u8], #payload_ty) },
            None => code! { (&[::core::primitive::u8],) },
        };
        let chunk = hasher::lower_tokens(
            code!(::core::primitive::u64::from_le_bytes(*__lhs)),
            self.ignore_case,
        );
        let last = hasher::lower_tokens(
            code!(
                __key
                    .last_chunk::<8>()
                    .map_or(0, |__last| ::core::primitive::u64::from_le_bytes(*__last))
            ),
            self.ignore_case,
        );
        let found = self.found(code!(1));
        let not_found = self.not_found();

        let fill = self.fill(table);

        code! {{
            #fill
            static __TABLE: [#row_ty; #slots_len] = [#(#rows),*];
            let __hash: #hash_ty = #hash;
            #locate
            if __entry.0.len() == __len
                && ::core::iter::Iterator::all(
                    &mut ::core::iter::Iterator::zip(
                        __key.as_chunks::<8>().0.iter(),
                        __entry.0.as_chunks::<8>().0,
                    ),
                    |(__lhs, __rhs)| #chunk == ::core::primitive::u64::from_le_bytes(*__rhs),
                )
                && #last
                    == __entry
                        .0
                        .last_chunk::<8>()
                        .map_or(0, |__last| ::core::primitive::u64::from_le_bytes(*__last))
            {
                #found
            } else {
                #not_found
            }
        }}
    }
}

fn is_statement(expr: &Expr) -> bool {
    let Expr::Block(block) = expr else {
        return false;
    };
    block.block.stmts.last().is_none_or(|stmt| match stmt {
        Stmt::Local(_) | Stmt::Item(_) => true,
        Stmt::Expr(_, semi) => semi.is_some(),
        Stmt::Macro(mac) => mac.semi_token.is_some(),
    })
}

fn token_count(tokens: TokenStream) -> usize {
    tokens
        .into_iter()
        .map(|token| match token {
            TokenTree::Group(group) => 1 + token_count(group.stream()),
            _ => 1,
        })
        .sum()
}
