/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use std::collections::HashSet;

const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyz0123456789-_";
const MIN_LEN: u64 = 3;
const LEN_SPREAD: u64 = 10;
const SEED: u64 = 0x9e37_79b9_7f4a_7c15;

pub fn generate(count: usize) -> Vec<String> {
    let mut state = SEED;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut seen = HashSet::with_capacity(count);
    let mut keys = Vec::with_capacity(count);
    while keys.len() < count {
        let lengths = next();
        let len = MIN_LEN + lengths % LEN_SPREAD + (lengths >> 32) % LEN_SPREAD;
        let key: String = (0..len)
            .map(|_| char::from(ALPHABET[(next() % ALPHABET.len() as u64) as usize]))
            .collect();
        if seen.insert(key.clone()) {
            keys.push(key);
        }
    }
    keys
}
