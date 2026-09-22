/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use proc_macro2::{Ident, Span, TokenStream};
use quote::{ToTokens, quote};

pub fn build_map(
    name: Expr,
    return_type: Option<Expr>,
    options: Vec<(Key, Option<Expr>)>,
    ignore_case: bool,
) -> proc_macro::TokenStream {
    let lookup_32 = build_lookup::<u32>(&name, return_type.as_ref(), &options, ignore_case);
    let lookup_64 = build_lookup::<u64>(&name, return_type.as_ref(), &options, ignore_case);

    match (lookup_32, lookup_64) {
        (Some(lookup_32), Some(lookup_64)) => quote! {{
            #[cfg(target_pointer_width = "64")]
            let __value = #lookup_64;
            #[cfg(not(target_pointer_width = "64"))]
            let __value = #lookup_32;
            __value
        }},
        (Some(lookup), None) | (None, Some(lookup)) => lookup,
        (None, None) => quote! { compile_error!("failed to resolve hash collision") },
    }
    .into()
}

fn build_lookup<H: PhfHash>(
    name: &Expr,
    return_type: Option<&Expr>,
    keys: &[(Key, Option<Expr>)],
    ignore_case: bool,
) -> Option<TokenStream> {
    let Phf {
        seed,
        pilots_table,
        map,
        free,
    } = generate_phf::<H>(keys)?;

    let mut min_key_size = usize::MAX;
    let mut max_key_size = 0;

    let hash_type = H::type_name();
    let key_prime = H::KEY_PRIME;
    let pilot_prime = H::PILOT_PRIME;
    let keys_len = keys.len();
    let pilots_len = H::from_len(pilots_table.len());
    let codomain_len = H::from_len(keys.len() + free.len());
    let keys_array = map.iter().map(|idx| {
        let (key, return_type) = &keys[*idx as usize];

        if key.len() < min_key_size {
            min_key_size = key.len();
        }
        if key.len() > max_key_size {
            max_key_size = key.len();
        }

        if let Some(return_type) = return_type {
            quote! {
                (#key, #return_type)
            }
        } else {
            quote! {
                #key
            }
        }
    });

    let (keys_def, keys_return, default_value) = if let Some(return_type) = return_type {
        let keys_def = quote! {
            &[(&[u8], #return_type)]
        };
        let compare_fnc = if ignore_case {
            quote! { __key.eq_ignore_ascii_case(value.0) }
        } else {
            quote! { __key.eq(value.0) }
        };
        let keys_return = quote! {
            if #compare_fnc  {
                Some(&value.1)
            } else {
                None
            }
        };
        let default_value = quote! {
            None
        };
        (keys_def, keys_return, default_value)
    } else {
        let keys_def = quote! {
            &[&[u8]]
        };
        let keys_return = if ignore_case {
            quote! {
                __key.eq_ignore_ascii_case(*value)
            }
        } else {
            quote! {
                __key.eq(*value)
            }
        };
        let default_value = quote! {
            false
        };
        (keys_def, keys_return, default_value)
    };
    let c = if ignore_case {
        quote! { c.to_ascii_lowercase() }
    } else {
        quote! { c }
    };

    Some(quote! {{
       static PILOTS_TABLE: &[u16] = &[#(#pilots_table),*];
       static FREE: &[u32] = &[#(#free),*];
       static KEYS: #keys_def = &[#(#keys_array),*];

       let __key = #name;

       if (#min_key_size..=#max_key_size).contains(&__key.len()) {
            let key_hash = __key.iter().fold(#seed, |h, &c| {
                h.wrapping_mul(#key_prime).wrapping_add(#c as #hash_type)
            });
            let pilot_hash = (PILOTS_TABLE[(key_hash % #pilots_len) as usize] as #hash_type).wrapping_mul(#pilot_prime);
            let idx = ((key_hash ^ pilot_hash) % #codomain_len) as usize;

            let value = if idx < #keys_len {
                &KEYS[idx]
            } else {
                &KEYS[FREE[idx - #keys_len] as usize]
            };

            #keys_return
        } else {
            #default_value
        }
    }})
}

/*
 * SPDX-FileCopyrightText: 2023 Darko Trifunovski & Nikolai Vazquez <https://github.com/dtrifuno/quickphf>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use syn::Expr;

use crate::Key;

const MAX_ALPHA: f64 = 0.99;
const MIN_C: f64 = 1.5;
const MAX_SEED_ATTEMPTS: u32 = 16;

/// Parameters for a PTHash perfect hash function.
pub struct Phf<H> {
    pub seed: H,
    pub pilots_table: Vec<u16>,
    pub map: Vec<u32>,
    pub free: Vec<u32>,
}

pub trait PhfHash: Copy + Ord + ToTokens {
    const KEY_PRIME: Self;
    const PILOT_PRIME: Self;

    fn type_name() -> Ident;
    fn from_len(len: usize) -> Self;
    fn seed(attempt: u32) -> Self;
    fn hash_key(key: &[u8], seed: Self) -> Self;
    fn hash_pilot_value(pilot_value: u16) -> Self;
    fn bucket(self, buckets_len: usize) -> usize;
    fn index(self, pilot_hash: Self, codomain_len: usize) -> usize;
}

macro_rules! impl_phf_hash {
    ($hash:ident, $key_prime:literal, $pilot_prime:literal, $seed_shift:literal) => {
        impl PhfHash for $hash {
            const KEY_PRIME: Self = $key_prime;
            const PILOT_PRIME: Self = $pilot_prime;

            fn type_name() -> Ident {
                Ident::new(stringify!($hash), Span::call_site())
            }

            fn from_len(len: usize) -> Self {
                len as Self
            }

            fn seed(attempt: u32) -> Self {
                Self::from(attempt) << $seed_shift
            }

            #[inline]
            fn hash_key(key: &[u8], seed: Self) -> Self {
                key.iter().fold(seed, |h, b| {
                    h.wrapping_mul(Self::KEY_PRIME).wrapping_add(*b as Self)
                })
            }

            #[inline]
            fn hash_pilot_value(pilot_value: u16) -> Self {
                Self::from(pilot_value).wrapping_mul(Self::PILOT_PRIME)
            }

            #[inline]
            fn bucket(self, buckets_len: usize) -> usize {
                (self % Self::from_len(buckets_len)) as usize
            }

            #[inline]
            fn index(self, pilot_hash: Self, codomain_len: usize) -> usize {
                ((self ^ pilot_hash) % Self::from_len(codomain_len)) as usize
            }
        }
    };
}

impl_phf_hash!(u64, 0x0100_0000_01b3, 0x517cc1b727220a95, 32);
impl_phf_hash!(u32, 0x01000193, 0x9e3779b9, 28);

/// Generate a perfect hash function using PTHash for the given collection of keys.
///
/// # Panics
///
/// Panics if `entries` contains a duplicate key.
pub fn generate_phf<H: PhfHash>(keys: &[(Key, Option<Expr>)]) -> Option<Phf<H>> {
    if keys.is_empty() {
        return Some(Phf {
            seed: H::seed(0),
            map: vec![],
            // These vectors have to be non-empty so that the number of buckets and codomain
            // length are non-zero, and thus can be used as divisors.
            pilots_table: vec![0],
            free: vec![0],
        });
    }

    let n = keys.len();
    let lg = n.ilog2() as f64;
    let c = MIN_C + 0.2 * lg;
    let buckets_len = if n > 1 {
        ((c * n as f64) / lg).ceil() as usize
    } else {
        1
    };

    let alpha = MAX_ALPHA - 0.001 * lg;
    let codomain_len = {
        let candidate = (n as f64 / alpha).ceil() as usize;
        candidate + (1 - candidate % 2)
    };

    (1..=MAX_SEED_ATTEMPTS)
        .find_map(|attempt| try_generate_phf(keys, buckets_len, codomain_len, H::seed(attempt)))
}

fn try_generate_phf<H: PhfHash>(
    entries: &[(Key, Option<Expr>)],
    buckets_len: usize,
    codomain_len: usize,
    seed: H,
) -> Option<Phf<H>> {
    // We begin by hashing the entries, assigning them to buckets, and checking for collisions.
    struct HashedEntry<T> {
        idx: usize,
        hash: T,
        bucket: usize,
    }

    let mut hashed_entries: Vec<_> = entries
        .iter()
        .enumerate()
        .map(|(idx, (entry, _))| {
            let hash = H::hash_key(entry.as_bytes(), seed);
            let bucket = hash.bucket(buckets_len);

            HashedEntry { idx, hash, bucket }
        })
        .collect();

    hashed_entries.sort_unstable_by_key(|e| (e.bucket, e.hash));

    for window in hashed_entries.as_slice().windows(2) {
        let e0 = &window[0];
        let e1 = &window[1];

        if e0.hash == e1.hash && e0.bucket == e1.bucket {
            assert!(
                entries[e0.idx].0 != entries[e1.idx].0,
                "duplicate keys at indices {} and {}",
                e0.idx,
                e1.idx
            );
            return None;
        }
    }

    //
    struct BucketData {
        idx: usize,
        start_idx: usize,
        size: usize,
    }

    let mut buckets = Vec::with_capacity(buckets_len);

    let mut start_idx = 0;
    for idx in 0..buckets_len {
        let size = hashed_entries[start_idx..]
            .iter()
            .take_while(|entry| entry.bucket == idx)
            .count();

        buckets.push(BucketData {
            idx,
            start_idx,
            size,
        });
        start_idx += size;
    }

    buckets.sort_unstable_by(|b1, b2| b1.size.cmp(&b2.size).reverse());

    let mut pilots_table = vec![0; buckets_len];

    // Using a sentinel value instead of an Option here allows us to avoid an expensive
    // reallocation. This is fine since the compiler cannot handle a static map with more than
    // a few million entries anyway.
    assert!((entries.len() as u64) < (u32::MAX as u64));
    const EMPTY: u32 = u32::MAX;
    let mut map = vec![EMPTY; codomain_len];

    let mut values_to_add = Vec::new();
    for bucket in buckets {
        let mut pilot_found = false;

        let bucket_start = bucket.start_idx;
        let bucket_end = bucket_start + bucket.size;
        let bucket_entries = &hashed_entries[bucket_start..bucket_end];

        'pilots: for pilot in 0u16..=u16::MAX {
            values_to_add.clear();
            let pilot_hash = H::hash_pilot_value(pilot);

            // Check for collisions with items from previous buckets.
            for entry in bucket_entries {
                let destination = entry.hash.index(pilot_hash, codomain_len);

                if map[destination] != EMPTY {
                    continue 'pilots;
                }

                values_to_add.push((entry.idx, destination));
            }

            // Check for collisions within this bucket.
            values_to_add.sort_unstable_by_key(|k| k.1);
            for window in values_to_add.as_slice().windows(2) {
                if window[0].1 == window[1].1 {
                    continue 'pilots;
                }
            }

            pilot_found = true;
            for &(idx, destination) in &values_to_add {
                map[destination] = idx as u32;
            }
            pilots_table[bucket.idx] = pilot;
            break;
        }

        if !pilot_found {
            return None;
        }
    }

    // At this point `map` is a table of size `n_prime`, but with `n` values.
    // We need to move the items from the back into the empty slots at the
    // front, and compute the vector `free` that will point to their new locations.
    let extra_slots = codomain_len - entries.len();
    let mut free = vec![0; extra_slots];

    let mut back_idx = entries.len();
    for front_idx in 0..entries.len() {
        if map[front_idx] != EMPTY {
            continue;
        }

        while map[back_idx] == EMPTY {
            back_idx += 1;
        }

        map[front_idx] = map[back_idx];
        free[back_idx - entries.len()] = front_idx as u32;
        back_idx += 1;
    }

    map.truncate(entries.len());

    Some(Phf {
        seed,
        pilots_table,
        map,
        free,
    })
}
