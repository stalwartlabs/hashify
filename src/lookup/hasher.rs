/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use proc_macro2::TokenStream;
use quote::ToTokens;

pub(crate) const SHORT_KEY_MAX_LEN: usize = 16;

const SEED_INCREMENT: u64 = 0x9e37_79b9_7f4a_7c15;
const MAX_EXPECTED_COLLISIONS: u128 = 8;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Words {
    pub a: u64,
    pub b: u64,
}

impl Words {
    pub(crate) fn of(key: &[u8]) -> Self {
        if let (Some(first), Some(last)) = (key.first_chunk::<8>(), key.last_chunk::<8>()) {
            Words {
                a: u64::from_le_bytes(*first),
                b: u64::from_le_bytes(*last),
            }
        } else if let (Some(first), Some(last)) = (key.first_chunk::<4>(), key.last_chunk::<4>()) {
            Words {
                a: u32::from_le_bytes(*first).into(),
                b: u32::from_le_bytes(*last).into(),
            }
        } else if let (Some(&first), Some(&middle), Some(&last)) =
            (key.first(), key.get(key.len() >> 1), key.last())
        {
            Words {
                a: first as u64 | (middle as u64) << 8 | (last as u64) << 16,
                b: 0,
            }
        } else {
            Words { a: 0, b: 0 }
        }
    }

    pub(crate) fn tokens(min_len: usize, max_len: usize, ignore_case: bool) -> TokenStream {
        let mut words = code! { (0u64, 0u64) };
        if min_len < 4 && max_len > 0 {
            let narrow = code! {
                (
                    __key[0] as ::core::primitive::u64
                        | (__key[__len >> 1] as ::core::primitive::u64) << 8
                        | (__key[__len - 1] as ::core::primitive::u64) << 16,
                    0u64,
                )
            };
            words = if min_len == 0 {
                code! { if __len > 0 { #narrow } else { #words } }
            } else {
                narrow
            };
        }
        if min_len < 8 && max_len >= 4 {
            words = code! {
                if let (
                    ::core::option::Option::Some(__first),
                    ::core::option::Option::Some(__last),
                ) = (__key.first_chunk::<4>(), __key.last_chunk::<4>())
                {
                    (
                        ::core::primitive::u32::from_le_bytes(*__first) as ::core::primitive::u64,
                        ::core::primitive::u32::from_le_bytes(*__last) as ::core::primitive::u64,
                    )
                } else {
                    #words
                }
            };
        }
        if max_len >= 8 {
            words = code! {
                if let (
                    ::core::option::Option::Some(__first),
                    ::core::option::Option::Some(__last),
                ) = (__key.first_chunk::<8>(), __key.last_chunk::<8>())
                {
                    (
                        ::core::primitive::u64::from_le_bytes(*__first),
                        ::core::primitive::u64::from_le_bytes(*__last),
                    )
                } else {
                    #words
                }
            };
        }
        if ignore_case {
            let lower_a = ascii_lowercase_tokens(code!(__words.0));
            let lower_b = ascii_lowercase_tokens(code!(__words.1));
            code! {{
                let __words: (::core::primitive::u64, ::core::primitive::u64) = #words;
                (#lower_a, #lower_b)
            }}
        } else {
            words
        }
    }
}

fn ascii_lowercase_tokens(word: TokenStream) -> TokenStream {
    code! {{
        let __word: ::core::primitive::u64 = #word;
        let __ascii = __word & 0x7f7f_7f7f_7f7f_7f7f;
        let __upper = (__ascii + 0x3f3f_3f3f_3f3f_3f3f)
            & !(__ascii + 0x2525_2525_2525_2525)
            & !__word
            & 0x8080_8080_8080_8080;
        __word | (__upper >> 2)
    }}
}

pub(crate) fn lower_tokens(word: TokenStream, ignore_case: bool) -> TokenStream {
    if ignore_case {
        ascii_lowercase_tokens(word)
    } else {
        word
    }
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(SEED_INCREMENT);
    let mut mixed = *state;
    mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    mixed ^ (mixed >> 31)
}

pub(crate) trait HashWord: Copy + Ord + ToTokens {
    const BITS: u32;
    fn ty() -> TokenStream;
    fn seeds(attempt: u32) -> [Self; 3];
    fn hash_short(words: Words, len: usize, seeds: &[Self; 3]) -> Self;
    fn hash_long(key: &[u8], seeds: &[Self; 3]) -> Self;
    fn bucket(self, buckets_len: usize) -> usize;
    fn slot(self, pilot: u8, slots_len: usize) -> usize;
    fn hash_short_tokens(seeds: &[Self; 3]) -> TokenStream;
    fn hash_long_tokens(seeds: &[Self; 3], ignore_case: bool) -> TokenStream;
    fn bucket_tokens(buckets_len: usize) -> TokenStream;
    fn slot_tokens(slots_len: usize) -> TokenStream;
    fn top(self, bits: u32) -> usize;
    fn top_tokens(bits: u32) -> TokenStream;
    fn hash_flat(words: Words, len: usize, seeds: &[Self; 3]) -> Self;
    fn hash_flat_tokens(seeds: &[Self; 3]) -> TokenStream;

    fn fits(keys_len: usize) -> bool {
        (keys_len as u128).saturating_pow(2) <= MAX_EXPECTED_COLLISIONS << (Self::BITS + 1)
    }
}

fn fold64(x: u64, y: u64) -> u64 {
    let product = (x as u128) * (y as u128);
    (product as u64) ^ ((product >> 64) as u64)
}

fn fold32(x: u32, y: u32) -> u32 {
    let product = (x as u64) * (y as u64);
    (product as u32) ^ ((product >> 32) as u32)
}

impl HashWord for u64 {
    const BITS: u32 = u64::BITS;

    fn ty() -> TokenStream {
        code!(::core::primitive::u64)
    }

    fn top(self, bits: u32) -> usize {
        (self >> (u64::BITS - bits)) as usize
    }

    fn top_tokens(bits: u32) -> TokenStream {
        let shift = u64::BITS - bits;
        code! { (__hash >> #shift) as ::core::primitive::usize }
    }

    fn hash_flat(words: Words, len: usize, seeds: &[Self; 3]) -> Self {
        (words.a ^ seeds[0]).wrapping_mul(words.b ^ (len as u64).wrapping_mul(seeds[1]))
    }

    fn hash_flat_tokens(seeds: &[Self; 3]) -> TokenStream {
        let [s0, s1, _] = seeds;
        code! {
            (__words.0 ^ #s0)
                .wrapping_mul(__words.1 ^ (__len as ::core::primitive::u64).wrapping_mul(#s1))
        }
    }

    fn seeds(attempt: u32) -> [Self; 3] {
        let mut state = u64::from(attempt);
        let [s0, s1, s2] = [(); 3].map(|_| splitmix64(&mut state));
        [s0 & u64::from(u16::MAX), s1 | 1, s2]
    }

    fn hash_short(words: Words, len: usize, seeds: &[Self; 3]) -> Self {
        fold64(
            words.a ^ seeds[0],
            words.b ^ (len as u64).wrapping_mul(seeds[1]),
        )
    }

    fn hash_long(key: &[u8], seeds: &[Self; 3]) -> Self {
        let (chunks, _) = key.as_chunks::<8>();
        let hash = chunks.iter().fold(
            seeds[0] ^ (key.len() as u64).wrapping_mul(seeds[1]),
            |hash, chunk| fold64(hash ^ u64::from_le_bytes(*chunk), seeds[1]),
        );
        let last = key
            .last_chunk::<8>()
            .map_or(0, |chunk| u64::from_le_bytes(*chunk));
        fold64(hash ^ last, seeds[2])
    }

    fn bucket(self, buckets_len: usize) -> usize {
        ((self as u128 * buckets_len as u128) >> 64) as usize
    }

    fn slot(self, pilot: u8, slots_len: usize) -> usize {
        let mixed = self.rotate_left(32).wrapping_mul(2 * pilot as u64 + 1);
        ((mixed as u128 * slots_len as u128) >> 64) as usize
    }

    fn hash_short_tokens(seeds: &[Self; 3]) -> TokenStream {
        let [s0, s1, _] = seeds;
        code! {{
            let __product = ((__words.0 ^ #s0) as ::core::primitive::u128)
                * ((__words.1 ^ (__len as ::core::primitive::u64).wrapping_mul(#s1))
                    as ::core::primitive::u128);
            (__product as ::core::primitive::u64) ^ ((__product >> 64) as ::core::primitive::u64)
        }}
    }

    fn hash_long_tokens(seeds: &[Self; 3], ignore_case: bool) -> TokenStream {
        let [s0, s1, s2] = seeds;
        let chunk = lower_tokens(
            code!(::core::primitive::u64::from_le_bytes(*__chunk)),
            ignore_case,
        );
        let last = lower_tokens(
            code!(
                __key
                    .last_chunk::<8>()
                    .map_or(0, |__last| ::core::primitive::u64::from_le_bytes(*__last))
            ),
            ignore_case,
        );
        code! {{
            let mut __state = #s0 ^ (__len as ::core::primitive::u64).wrapping_mul(#s1);
            for __chunk in __key.as_chunks::<8>().0 {
                let __product = ((__state ^ #chunk) as ::core::primitive::u128)
                    * (#s1 as ::core::primitive::u128);
                __state = (__product as ::core::primitive::u64)
                    ^ ((__product >> 64) as ::core::primitive::u64);
            }
            let __product =
                ((__state ^ #last) as ::core::primitive::u128) * (#s2 as ::core::primitive::u128);
            (__product as ::core::primitive::u64) ^ ((__product >> 64) as ::core::primitive::u64)
        }}
    }

    fn bucket_tokens(buckets_len: usize) -> TokenStream {
        let buckets_len = buckets_len as u128;
        code! {
            ((__hash as ::core::primitive::u128 * #buckets_len) >> 64) as ::core::primitive::usize
        }
    }

    fn slot_tokens(slots_len: usize) -> TokenStream {
        let slots_len = slots_len as u128;
        code! {
            ((__hash.rotate_left(32).wrapping_mul(2 * __pilot as ::core::primitive::u64 + 1)
                as ::core::primitive::u128
                * #slots_len)
                >> 64) as ::core::primitive::usize
        }
    }
}

impl HashWord for u32 {
    const BITS: u32 = u32::BITS;

    fn ty() -> TokenStream {
        code!(::core::primitive::u32)
    }

    fn top(self, bits: u32) -> usize {
        (self >> (u32::BITS - bits)) as usize
    }

    fn top_tokens(bits: u32) -> TokenStream {
        let shift = u32::BITS - bits;
        code! { (__hash >> #shift) as ::core::primitive::usize }
    }

    fn hash_flat(words: Words, len: usize, seeds: &[Self; 3]) -> Self {
        Self::hash_short(words, len, seeds)
    }

    fn hash_flat_tokens(seeds: &[Self; 3]) -> TokenStream {
        Self::hash_short_tokens(seeds)
    }

    fn seeds(attempt: u32) -> [Self; 3] {
        let mut state = u64::from(attempt);
        let [s0, s1, s2] = [(); 3].map(|_| splitmix64(&mut state) as u32);
        [s0, s1, s2 | 1]
    }

    fn hash_short(words: Words, len: usize, seeds: &[Self; 3]) -> Self {
        let upper = fold32(words.a as u32 ^ seeds[0], (words.a >> 32) as u32 ^ seeds[1]);
        fold32(
            upper ^ words.b as u32,
            (words.b >> 32) as u32 ^ (len as u32).wrapping_mul(seeds[2]),
        )
    }

    fn hash_long(key: &[u8], seeds: &[Self; 3]) -> Self {
        let (chunks, _) = key.as_chunks::<4>();
        let hash = chunks.iter().fold(
            seeds[0] ^ (key.len() as u32).wrapping_mul(seeds[2]),
            |hash, chunk| fold32(hash ^ u32::from_le_bytes(*chunk), seeds[1]),
        );
        let last = key
            .last_chunk::<4>()
            .map_or(0, |chunk| u32::from_le_bytes(*chunk));
        fold32(hash ^ last, seeds[2])
    }

    fn bucket(self, buckets_len: usize) -> usize {
        ((self as u64 * buckets_len as u64) >> 32) as usize
    }

    fn slot(self, pilot: u8, slots_len: usize) -> usize {
        let mixed = self.rotate_left(16).wrapping_mul(2 * pilot as u32 + 1);
        ((mixed as u64 * slots_len as u64) >> 32) as usize
    }

    fn hash_short_tokens(seeds: &[Self; 3]) -> TokenStream {
        let [s0, s1, s2] = seeds;
        code! {{
            let __product = ((__words.0 as ::core::primitive::u32 ^ #s0) as ::core::primitive::u64)
                * (((__words.0 >> 32) as ::core::primitive::u32 ^ #s1) as ::core::primitive::u64);
            let __upper = (__product as ::core::primitive::u32)
                ^ ((__product >> 32) as ::core::primitive::u32);
            let __product = ((__upper ^ __words.1 as ::core::primitive::u32)
                as ::core::primitive::u64)
                * (((__words.1 >> 32) as ::core::primitive::u32
                    ^ (__len as ::core::primitive::u32).wrapping_mul(#s2))
                    as ::core::primitive::u64);
            (__product as ::core::primitive::u32) ^ ((__product >> 32) as ::core::primitive::u32)
        }}
    }

    fn hash_long_tokens(seeds: &[Self; 3], ignore_case: bool) -> TokenStream {
        let [s0, s1, s2] = seeds;
        let lower = |word: TokenStream| {
            let word = lower_tokens(code!((#word) as ::core::primitive::u64), ignore_case);
            code!((#word) as ::core::primitive::u32)
        };
        let chunk = lower(code!(::core::primitive::u32::from_le_bytes(*__chunk)));
        let last = lower(code!(__key.last_chunk::<4>().map_or(0, |__last| {
            ::core::primitive::u32::from_le_bytes(*__last)
        })));
        code! {{
            let mut __state = #s0 ^ (__len as ::core::primitive::u32).wrapping_mul(#s2);
            for __chunk in __key.as_chunks::<4>().0 {
                let __product = ((__state ^ #chunk) as ::core::primitive::u64)
                    * (#s1 as ::core::primitive::u64);
                __state = (__product as ::core::primitive::u32)
                    ^ ((__product >> 32) as ::core::primitive::u32);
            }
            let __product =
                ((__state ^ #last) as ::core::primitive::u64) * (#s2 as ::core::primitive::u64);
            (__product as ::core::primitive::u32) ^ ((__product >> 32) as ::core::primitive::u32)
        }}
    }

    fn bucket_tokens(buckets_len: usize) -> TokenStream {
        let buckets_len = buckets_len as u64;
        code! {
            ((__hash as ::core::primitive::u64 * #buckets_len) >> 32) as ::core::primitive::usize
        }
    }

    fn slot_tokens(slots_len: usize) -> TokenStream {
        let slots_len = slots_len as u64;
        code! {
            ((__hash.rotate_left(16).wrapping_mul(2 * __pilot as ::core::primitive::u32 + 1)
                as ::core::primitive::u64
                * #slots_len)
                >> 32) as ::core::primitive::usize
        }
    }
}
