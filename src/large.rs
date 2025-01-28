/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use proc_macro::TokenStream;
use quote::quote;

pub fn build_map(
    name: Expr,
    return_type: Option<Expr>,
    options: Vec<(Key, Option<Expr>)>,
    ignore_case: bool,
) -> TokenStream {
    let Phf {
        seed,
        pilots_table,
        map,
        free,
        keys,
    } = generate_phf(options);

    let mut min_key_size = usize::MAX;
    let mut max_key_size = 0;

    let keys_len = keys.len();
    let pilots_len = pilots_table.len();
    let codomain_len = (keys.len() + free.len()) as u64;
    let pilots_array = pilots_table.iter().map(|x| quote!(#x));
    let free_array = free.iter().map(|x| quote!(#x));
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
            quote! { __key == value.0 }
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
                __key.eq_ignore_ascii_case(value)
            }
        } else {
            quote! {
                __key == value
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

    TokenStream::from(quote! {{
       static PILOTS_TABLE: &[u16] = &[#(#pilots_array),*];
       static FREE: &[u32] = &[#(#free_array),*];
       static KEYS: #keys_def = &[#(#keys_array),*];

       let __key = #name;

       if (#min_key_size..=#max_key_size).contains(&__key.len()) {
            let key_hash = __key.iter().fold(#seed, |h, &c| {
                h.wrapping_mul(0x0100_0000_01b3).wrapping_add(#c as u64)
            });
            let pilot_hash = (PILOTS_TABLE[key_hash as usize % #pilots_len] as u64).wrapping_mul( 0x517cc1b727220a95);
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

#[inline]
fn ilog2(n: u64) -> u32 {
    63 - n.leading_zeros()
}

/// Parameters for a PTHash perfect hash function.
pub struct Phf {
    pub seed: u64,
    pub pilots_table: Vec<u16>,
    pub map: Vec<u32>,
    pub free: Vec<u32>,
    pub keys: Vec<(Key, Option<Expr>)>,
}

#[inline]
pub fn hash_key(key: &[u8], seed: u64) -> u64 {
    key.iter().fold(seed, |h, b| {
        h.wrapping_mul(0x0100_0000_01b3).wrapping_add(*b as u64)
    })
}

#[inline]
pub fn hash_pilot_value(pilot_value: u16) -> u64 {
    (pilot_value as u64).wrapping_mul(0x517cc1b727220a95)
}

#[inline]
pub fn get_bucket(key_hash: u64, buckets: u64) -> usize {
    (key_hash % buckets) as usize
}

#[inline]
pub fn get_index(key_hash: u64, pilot_hash: u64, codomain_len: u64) -> usize {
    ((key_hash ^ pilot_hash) % codomain_len) as usize
}

/// Generate a perfect hash function using PTHash for the given collection of keys.
///
/// # Panics
///
/// Panics if `entries` contains a duplicate key.
pub fn generate_phf(keys: Vec<(Key, Option<Expr>)>) -> Phf {
    if keys.is_empty() {
        return Phf {
            seed: 0,
            map: vec![],
            // These vectors have to be non-empty so that the number of buckets and codomain
            // length are non-zero, and thus can be used as divisors.
            pilots_table: vec![0],
            free: vec![0],
            keys: vec![],
        };
    }

    let n = keys.len() as u64;
    let lg = ilog2(n) as f64;
    let c = MIN_C + 0.2 * lg;
    let buckets_len = if n > 1 {
        ((c * n as f64) / lg).ceil() as u64
    } else {
        1
    };

    let alpha = MAX_ALPHA - 0.001 * lg;
    let codomain_len = {
        let candidate = (n as f64 / alpha).ceil() as u64;
        candidate + (1 - candidate % 2)
    };

    let mut phf = (1..)
        .find_map(|n| try_generate_phf(&keys, buckets_len, codomain_len, n << 32))
        .expect("failed to resolve hash collision");
    phf.keys = keys;
    phf
}

fn try_generate_phf(
    entries: &[(Key, Option<Expr>)],
    buckets_len: u64,
    codomain_len: u64,
    seed: u64,
) -> Option<Phf> {
    // We begin by hashing the entries, assigning them to buckets, and checking for collisions.
    struct HashedEntry {
        idx: usize,
        hash: u64,
        bucket: usize,
    }

    let mut hashed_entries: Vec<_> = entries
        .iter()
        .enumerate()
        .map(|(idx, (entry, _))| {
            let hash = hash_key(entry.as_bytes(), seed);
            let bucket = get_bucket(hash, buckets_len);

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

    let mut buckets = Vec::with_capacity(buckets_len as usize);

    let mut start_idx = 0;
    for idx in 0..buckets_len as usize {
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

    let mut pilots_table = vec![0; buckets_len as usize];

    // Using a sentinel value instead of an Option here allows us to avoid an expensive
    // reallocation. This is fine since the compiler cannot handle a static map with more than
    // a few million entries anyway.
    assert!((entries.len() as u64) < (u32::MAX as u64));
    const EMPTY: u32 = u32::MAX;
    let mut map = vec![EMPTY; codomain_len as usize];

    let mut values_to_add = Vec::new();
    for bucket in buckets {
        let mut pilot_found = false;

        let bucket_start = bucket.start_idx;
        let bucket_end = bucket_start + bucket.size;
        let bucket_entries = &hashed_entries[bucket_start..bucket_end];

        'pilots: for pilot in 0u16..=u16::MAX {
            values_to_add.clear();
            let pilot_hash = hash_pilot_value(pilot);

            // Check for collisions with items from previous buckets.
            for entry in bucket_entries {
                let destination = get_index(entry.hash, pilot_hash, codomain_len);

                if map[destination as usize] != EMPTY {
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
    let extra_slots = codomain_len as usize - entries.len();
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
        keys: vec![],
        seed,
        pilots_table,
        map,
        free,
    })
}
