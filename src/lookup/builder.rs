/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use super::hasher::HashWord;
use std::collections::BinaryHeap;

const LOAD_FACTORS_PER_MILLE: [u64; 5] = [1000, 995, 990, 980, 950];
const BUCKET_SIZES_IN_TENTHS: [u64; 5] = [30, 25, 20, 15, 10];
const SEEDS_PER_CONFIG: u32 = 3;
const RECENT_BUCKETS: usize = 16;
const EMPTY: u32 = u32::MAX;
const MIN_EVICTION_COST: usize = 1;
const FLAT_ATTEMPTS: u32 = 16384;
const FLAT_MAX_COLLIDING_PAIRS_PER_SLOT_IN_MILLIONTHS: u64 = 8_317_766;
const FLAT_MAX_GROWTH: usize = 8;

pub(crate) struct Mphf<H> {
    pub seeds: [H; 3],
    pub pilots: Vec<u8>,
    pub slots: Vec<Option<usize>>,
}

pub(crate) fn build<H: HashWord, K>(
    keys: &[K],
    hash: impl Fn(&K, &[H; 3]) -> H,
) -> Option<Mphf<H>> {
    let keys_len = keys.len();
    let mut attempt = 0;
    for load_factor in LOAD_FACTORS_PER_MILLE {
        let slots_len = ceil_ratio(keys_len, 1000, load_factor).max(keys_len);
        for bucket_size in BUCKET_SIZES_IN_TENTHS {
            let buckets_len = ceil_ratio(keys_len, 10, bucket_size).max(1);
            for _ in 0..SEEDS_PER_CONFIG {
                attempt += 1;
                let seeds = H::seeds(attempt);
                let hashes: Vec<H> = keys.iter().map(|key| hash(key, &seeds)).collect();
                if let Some((pilots, slots)) = Placement::new(&hashes, buckets_len, slots_len)
                    .and_then(|placement| placement.run())
                {
                    return Some(Mphf {
                        seeds,
                        pilots,
                        slots,
                    });
                }
            }
        }
    }
    None
}

fn ceil_ratio(value: usize, numerator: u64, denominator: u64) -> usize {
    usize::try_from((value as u64 * numerator).div_ceil(denominator)).unwrap_or(usize::MAX)
}

pub(crate) fn build_flat<H: HashWord, K>(
    keys: &[K],
    hash: impl Fn(&K, &[H; 3]) -> H,
) -> Option<Mphf<H>> {
    let keys_len = keys.len();
    let min_slots = keys_len.next_power_of_two().max(2);
    let mut owners = Vec::new();
    std::iter::successors(Some(min_slots), |slots_len| Some(slots_len * 2))
        .take_while(|&slots_len| slots_len <= min_slots * FLAT_MAX_GROWTH)
        .filter(|&slots_len| {
            let pairs = (keys_len * keys_len.saturating_sub(1) / 2) as u64;
            pairs * 1_000_000 <= slots_len as u64 * FLAT_MAX_COLLIDING_PAIRS_PER_SLOT_IN_MILLIONTHS
        })
        .find_map(|slots_len| {
            let bits = slots_len.trailing_zeros();
            (1..=FLAT_ATTEMPTS).find_map(|attempt| {
                let seeds = H::seeds(attempt);
                owners.clear();
                owners.resize(slots_len, None);
                keys.iter()
                    .enumerate()
                    .all(|(idx, key)| owners[hash(key, &seeds).top(bits)].replace(idx).is_none())
                    .then(|| Mphf {
                        seeds,
                        pilots: Vec::new(),
                        slots: owners.clone(),
                    })
            })
        })
}

struct Placement<H> {
    keys: Vec<u32>,
    hashes: Vec<H>,
    starts: Vec<u32>,
    pilots: Vec<u8>,
    owners: Vec<u32>,
}

impl<H: HashWord> Placement<H> {
    fn new(hashes: &[H], buckets_len: usize, slots_len: usize) -> Option<Self> {
        let buckets: Vec<usize> = hashes.iter().map(|hash| hash.bucket(buckets_len)).collect();
        let mut starts = vec![0u32; buckets_len + 1];
        for &bucket in &buckets {
            starts[bucket + 1] += 1;
        }
        for bucket in 0..buckets_len {
            starts[bucket + 1] += starts[bucket];
        }

        let mut next = starts.clone();
        let mut order = vec![0u32; hashes.len()];
        for (&bucket, idx) in buckets.iter().zip(0..) {
            order[next[bucket] as usize] = idx;
            next[bucket] += 1;
        }
        let mut sorted: Vec<(H, u32)> = order
            .into_iter()
            .map(|idx| (hashes[idx as usize], idx))
            .collect();
        for bounds in starts.windows(2) {
            let bucket = &mut sorted[bounds[0] as usize..bounds[1] as usize];
            if bucket.len() > 1 {
                bucket.sort_unstable();
                if bucket.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                    return None;
                }
            }
        }
        let (hashes, keys) = sorted.into_iter().unzip();

        Some(Placement {
            keys,
            hashes,
            starts,
            pilots: vec![0; buckets_len],
            owners: vec![EMPTY; slots_len],
        })
    }

    fn range(&self, bucket: u32) -> std::ops::Range<usize> {
        let bucket = bucket as usize;
        self.starts[bucket] as usize..self.starts[bucket + 1] as usize
    }

    fn size(&self, bucket: u32) -> usize {
        let bucket = bucket as usize;
        (self.starts[bucket + 1] - self.starts[bucket]) as usize
    }

    fn free_pilot(&self, bucket: u32, slots: &mut Vec<usize>) -> Option<u8> {
        let hashes = &self.hashes[self.range(bucket)];
        let owners = self.owners.as_slice();
        let slots_len = owners.len();
        if let [hash] = hashes {
            slots.clear();
            for pilot in 0..=u8::MAX {
                let slot = hash.slot(pilot, slots_len);
                if owners[slot] == EMPTY {
                    slots.push(slot);
                    return Some(pilot);
                }
            }
            return None;
        }
        'pilots: for pilot in 0..=u8::MAX {
            slots.clear();
            for hash in hashes {
                let slot = hash.slot(pilot, slots_len);
                if owners[slot] != EMPTY || slots.contains(&slot) {
                    continue 'pilots;
                }
                slots.push(slot);
            }
            return Some(pilot);
        }
        None
    }

    fn cheapest_pilot(
        &self,
        bucket: u32,
        recent: &[u32],
        slots: &mut Vec<usize>,
        victims: &mut Vec<u32>,
    ) -> Option<u8> {
        let hashes = &self.hashes[self.range(bucket)];
        let owners = self.owners.as_slice();
        let slots_len = owners.len();
        let mut best: Option<(usize, u8)> = None;
        if let [hash] = hashes {
            for pilot in 0..=u8::MAX {
                let owner = owners[hash.slot(pilot, slots_len)];
                if owner == EMPTY {
                    return Some(pilot);
                }
                let size = self.size(owner);
                let cost = size * size;
                if best.is_some_and(|(best_cost, _)| cost >= best_cost) || recent.contains(&owner) {
                    continue;
                }
                if cost == MIN_EVICTION_COST {
                    return Some(pilot);
                }
                best = Some((cost, pilot));
            }
            return best.map(|(_, pilot)| pilot);
        }
        'pilots: for pilot in 0..=u8::MAX {
            slots.clear();
            for hash in hashes {
                let slot = hash.slot(pilot, slots_len);
                if slots.contains(&slot) {
                    continue 'pilots;
                }
                slots.push(slot);
            }
            victims.clear();
            let mut cost = 0;
            for &slot in slots.iter() {
                let owner = owners[slot];
                if owner == EMPTY || victims.contains(&owner) {
                    continue;
                }
                let size = self.size(owner);
                cost += size * size;
                if best.is_some_and(|(best_cost, _)| cost >= best_cost) || recent.contains(&owner) {
                    continue 'pilots;
                }
                victims.push(owner);
            }
            if cost == MIN_EVICTION_COST {
                return Some(pilot);
            }
            if best.is_none_or(|(best_cost, _)| cost < best_cost) {
                best = Some((cost, pilot));
            }
        }
        best.map(|(_, pilot)| pilot)
    }

    fn slots(&self, bucket: u32, pilot: u8) -> impl Iterator<Item = usize> + '_ {
        let slots_len = self.owners.len();
        self.hashes[self.range(bucket)]
            .iter()
            .map(move |hash| hash.slot(pilot, slots_len))
    }

    fn evict(&mut self, bucket: u32) {
        let slots_len = self.owners.len();
        let pilot = self.pilots[bucket as usize];
        for hash in &self.hashes[self.range(bucket)] {
            self.owners[hash.slot(pilot, slots_len)] = EMPTY;
        }
    }

    fn run(mut self) -> Option<(Vec<u8>, Vec<Option<usize>>)> {
        let buckets_len = self.pilots.len();
        let max_evictions = self.hashes.len() / 4 + 1024;
        let mut queue: BinaryHeap<(usize, u32)> = (0..buckets_len as u32)
            .map(|bucket| (self.size(bucket), bucket))
            .filter(|&(size, _)| size > 0)
            .collect();
        let mut recent = [EMPTY; RECENT_BUCKETS];
        let mut evictions = 0;
        let mut forced = 0;
        let mut slots = Vec::new();
        let mut victims = Vec::new();

        while let Some((_, bucket)) = queue.pop() {
            let pilot = match self.free_pilot(bucket, &mut slots) {
                Some(pilot) => pilot,
                None => {
                    let pilot = self.cheapest_pilot(bucket, &recent, &mut slots, &mut victims)?;
                    slots.clear();
                    slots.extend(self.slots(bucket, pilot));
                    for &slot in &slots {
                        let owner = self.owners[slot];
                        if owner != EMPTY {
                            self.evict(owner);
                            queue.push((self.size(owner), owner));
                            evictions += 1;
                        }
                    }
                    if evictions > max_evictions {
                        return None;
                    }
                    recent[forced % RECENT_BUCKETS] = bucket;
                    forced += 1;
                    pilot
                }
            };
            self.pilots[bucket as usize] = pilot;
            for &slot in &slots {
                self.owners[slot] = bucket;
            }
        }

        let mut slots = vec![None; self.owners.len()];
        for bucket in 0..buckets_len as u32 {
            let placed = self.slots(bucket, self.pilots[bucket as usize]);
            for (slot, &key) in placed.zip(&self.keys[self.range(bucket)]) {
                slots[slot] = Some(key as usize);
            }
        }

        Some((self.pilots, slots))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lookup::hasher::{SHORT_KEY_MAX_LEN, Words};

    fn keys(count: usize, seed: u64) -> Vec<Vec<u8>> {
        let mut state = seed;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut keys = std::collections::BTreeSet::new();
        while keys.len() < count {
            let len = 1 + (next() % 40) as usize;
            keys.insert((0..len).map(|_| next() as u8).collect::<Vec<u8>>());
        }
        keys.into_iter().collect()
    }

    fn hash<H: HashWord>(key: &[u8], seeds: &[H; 3]) -> H {
        if key.len() <= SHORT_KEY_MAX_LEN {
            H::hash_short(Words::of(key), key.len(), seeds)
        } else {
            H::hash_long(key, seeds)
        }
    }

    fn assert_minimal_perfect<H: HashWord>(keys: &[Vec<u8>]) {
        let mphf =
            build::<H, _>(keys, |key, seeds| hash(key, seeds)).expect("construction succeeds");
        assert!(mphf.slots.len() >= keys.len());
        let mut seen = vec![false; keys.len()];
        for (idx, key) in keys.iter().enumerate() {
            let hash = hash(key, &mphf.seeds);
            let pilot = mphf.pilots[hash.bucket(mphf.pilots.len())];
            let slot = hash.slot(pilot, mphf.slots.len());
            assert_eq!(
                mphf.slots[slot],
                Some(idx),
                "key {idx} of {} lands in a foreign slot",
                keys.len()
            );
            assert!(!seen[idx]);
            seen[idx] = true;
        }
    }

    fn assert_flat<K: AsRef<[u8]>>(keys: &[K]) {
        let inputs: Vec<(Words, usize)> = keys
            .iter()
            .map(|key| (Words::of(key.as_ref()), key.as_ref().len()))
            .collect();
        let flat = build_flat::<u64, _>(&inputs, |&(words, len), seeds| {
            u64::hash_flat(words, len, seeds)
        })
        .expect("flat construction succeeds");
        assert!(flat.pilots.is_empty());
        assert!(flat.slots.len().is_power_of_two());
        let bits = flat.slots.len().trailing_zeros();
        for (idx, &(words, len)) in inputs.iter().enumerate() {
            let hash = u64::hash_flat(words, len, &flat.seeds);
            assert_eq!(flat.slots[hash.top(bits)], Some(idx));
        }
    }

    #[test]
    fn builds_minimal_perfect_hash_functions() {
        for count in (1..=64).chain([100, 255, 256, 257, 1000, 2125, 5000]) {
            let keys = keys(count, count as u64 + 1);
            assert_minimal_perfect::<u64>(&keys);
            assert_minimal_perfect::<u32>(&keys);
        }
    }

    #[test]
    fn builds_collision_free_flat_tables() {
        for count in 1..=64 {
            assert_flat(&keys(count, count as u64 + 100));
        }
    }

    #[test]
    fn flat_tables_separate_keys_sharing_canonical_words() {
        assert_flat::<&[u8]>(&[
            b"i", b"ii", b"iii", b"iv", b"v", b"vi", b"vii", b"viii", b"ix", b"x", b"xi", b"xii",
            b"xiii", b"xiv", b"xv", b"xvi", b"xvii", b"xviii", b"xix", b"xx",
        ]);
        assert_flat::<&[u8]>(&[
            b"of", b"off", b"to", b"too", b"a", b"aa", b"in", b"on", b"at", b"it", b"is", b"be",
            b"we", b"he", b"by", b"or", b"an", b"as",
        ]);
        assert_flat::<&[u8]>(&[
            b"",
            b"\0",
            b"\0\0",
            b"abab",
            b"ababab",
            b"\0\0\0",
            b"\0\0\0\0",
            b"aaaa",
            b"aaaaa",
            b"aaaaaaaa",
            b"aaaaaaaaa",
            b"get",
            b"head",
            b"post",
            b"put",
            b"patch",
            b"delete",
        ]);
    }

    #[test]
    fn narrow_hashes_are_skipped_past_the_birthday_bound() {
        assert!(u32::fits(1 << 18));
        assert!(!u32::fits((1 << 18) + 1));
        // 2^34 keys do not fit in a 32-bit usize.
        #[cfg(target_pointer_width = "64")]
        assert!(u64::fits(1 << 34));
    }

    #[test]
    fn small_sets_are_minimal() {
        for count in [1, 2, 3, 10, 100, 1000, 2125] {
            let keys = keys(count, 7);
            let mphf = build::<u64, _>(&keys, |key, seeds| hash(key, seeds))
                .expect("construction succeeds");
            assert_eq!(mphf.slots.len(), keys.len());
        }
    }
}
