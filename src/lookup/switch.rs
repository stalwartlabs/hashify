/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use proc_macro2::{Span, TokenStream};
use std::collections::BTreeMap;
use syn::LitByteStr;

pub(crate) struct Switch<'x> {
    keys: &'x [&'x [u8]],
    ignore_case: bool,
}

pub(crate) struct Leaves<'x> {
    pub found: &'x dyn Fn(usize) -> TokenStream,
    pub missing: TokenStream,
}

#[derive(Clone, Copy)]
enum Selector {
    Position(usize),
    Xor(usize, usize),
}

enum Node {
    Leaf(usize),
    Dispatch {
        selector: Selector,
        arms: Vec<(u8, Node)>,
    },
}

impl Selector {
    fn byte(self, key: &[u8]) -> u8 {
        match self {
            Selector::Position(pos) => key[pos],
            Selector::Xor(left, right) => key[left] ^ key[right],
        }
    }

    fn candidates(positions: &[usize]) -> impl Iterator<Item = Selector> + '_ {
        positions.iter().map(|&pos| Selector::Position(pos)).chain(
            positions.iter().enumerate().flat_map(move |(idx, &left)| {
                positions
                    .iter()
                    .skip(idx + 1)
                    .map(move |&right| Selector::Xor(left, right))
            }),
        )
    }
}

impl<'x> Switch<'x> {
    pub(crate) fn new(keys: &'x [&'x [u8]], ignore_case: bool) -> Self {
        Switch { keys, ignore_case }
    }

    pub(crate) fn tokens(&self, leaves: &Leaves<'_>) -> TokenStream {
        let all: Vec<usize> = (0..self.keys.len()).collect();
        let lens = self.keys.iter().map(|key| key.len());
        let missing = &leaves.missing;
        let (Some(min_len), Some(max_len)) = (lens.clone().min(), lens.max()) else {
            return missing.clone();
        };

        if !(min_len == 1 && max_len > 1)
            && let Some(node) = self.dispatch(&all, min_len, false)
        {
            let node = self.node_tokens(&node, leaves);
            return code! {
                if (#min_len..=#max_len).contains(&__len) { #node } else { #missing }
            };
        }

        let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for (idx, key) in self.keys.iter().enumerate() {
            groups.entry(key.len()).or_default().push(idx);
        }
        let arms = groups.iter().map(|(&len, group)| match group.as_slice() {
            &[idx] => {
                let matches = self.matches(idx);
                let found = (leaves.found)(idx);
                code! { #len if #matches => #found, }
            }
            group => {
                let node = self
                    .dispatch(group, len, true)
                    .expect("keys of equal length are always separable");
                let node = self.node_tokens(&node, leaves);
                code! { #len => #node, }
            }
        });
        code! {
            match __len {
                #(#arms)*
                _ => #missing,
            }
        }
    }

    fn dispatch(&self, group: &[usize], len: usize, is_final: bool) -> Option<Node> {
        let leaves = |selector: Selector| Node::Dispatch {
            selector,
            arms: group
                .iter()
                .map(|&idx| (selector.byte(self.keys[idx]), Node::Leaf(idx)))
                .collect(),
        };
        if len == 1 && is_final {
            return Some(leaves(Selector::Position(0)));
        }

        let positions = self.varying_positions(group, len);
        let mut best: Option<(usize, Selector)> = None;
        for selector in Selector::candidates(&positions) {
            let mut seen = [false; 256];
            let distinct = group
                .iter()
                .filter(|&&idx| {
                    !std::mem::replace(&mut seen[selector.byte(self.keys[idx]) as usize], true)
                })
                .count();
            if distinct == group.len() {
                return Some(leaves(selector));
            }
            if best.is_none_or(|(best_distinct, _)| distinct > best_distinct) {
                best = Some((distinct, selector));
            }
        }

        let (_, selector) = best.filter(|_| is_final)?;
        let mut buckets: BTreeMap<u8, Vec<usize>> = BTreeMap::new();
        for &idx in group {
            buckets
                .entry(selector.byte(self.keys[idx]))
                .or_default()
                .push(idx);
        }
        let arms = buckets
            .into_iter()
            .map(|(byte, bucket)| match bucket.as_slice() {
                &[idx] => Some((byte, Node::Leaf(idx))),
                bucket => Some((byte, self.dispatch(bucket, len, true)?)),
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Node::Dispatch { selector, arms })
    }

    fn varying_positions(&self, group: &[usize], len: usize) -> Vec<usize> {
        (0..len)
            .filter(|&pos| {
                let mut bytes = group.iter().map(|&idx| self.keys[idx][pos]);
                bytes
                    .next()
                    .is_some_and(|first| bytes.any(|byte| byte != first))
            })
            .collect()
    }

    fn matches(&self, idx: usize) -> TokenStream {
        let key = LitByteStr::new(self.keys[idx], Span::mixed_site());
        if self.ignore_case {
            code! { __key.eq_ignore_ascii_case(#key) }
        } else {
            code! { __key == #key }
        }
    }

    fn selector_tokens(&self, selector: Selector) -> TokenStream {
        let byte = |pos: usize| {
            if self.ignore_case {
                code! { __key[#pos].to_ascii_lowercase() }
            } else {
                code! { __key[#pos] }
            }
        };
        match selector {
            Selector::Position(pos) => byte(pos),
            Selector::Xor(left, right) => {
                let (left, right) = (byte(left), byte(right));
                code! { #left ^ #right }
            }
        }
    }

    fn node_tokens(&self, node: &Node, leaves: &Leaves<'_>) -> TokenStream {
        let missing = &leaves.missing;
        match node {
            &Node::Leaf(idx) => {
                let matches = self.matches(idx);
                let found = (leaves.found)(idx);
                code! { if #matches { #found } else { #missing } }
            }
            Node::Dispatch { selector, arms } => {
                let selector = self.selector_tokens(*selector);
                let arms = arms.iter().map(|(byte, node)| match node {
                    &Node::Leaf(idx) if self.keys[idx].len() == 1 => {
                        let found = (leaves.found)(idx);
                        code! { #byte => #found, }
                    }
                    &Node::Leaf(idx) => {
                        let matches = self.matches(idx);
                        let found = (leaves.found)(idx);
                        code! { #byte if #matches => #found, }
                    }
                    node => {
                        let node = self.node_tokens(node, leaves);
                        code! { #byte => #node, }
                    }
                });
                code! {
                    match #selector {
                        #(#arms)*
                        _ => #missing,
                    }
                }
            }
        }
    }
}
