#![doc = include_str!("../README.md")]
/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

mod large;
mod tiny;

use std::collections::HashMap;

use large::build_map;
use proc_macro::TokenStream;
use syn::punctuated::Punctuated;
use syn::LitStr;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, Expr, Result, Token,
};
use tiny::build_tiny_map;

struct MapInput {
    name: Expr,
    pairs: Punctuated<KeyValue, Token![,]>,
}

struct BigMapInput {
    name: Expr,
    return_type: Expr,
    pairs: Punctuated<KeyValue, Token![,]>,
}

struct SetInput {
    name: Expr,
    pairs: Punctuated<Key, Token![,]>,
}

impl Parse for BigMapInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let return_type: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let pairs = input.parse_terminated(KeyValue::parse, Token![,])?;
        Ok(BigMapInput {
            name,
            return_type,
            pairs,
        })
    }
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

#[proc_macro]
pub fn map(input: TokenStream) -> TokenStream {
    let BigMapInput {
        name,
        return_type,
        pairs,
    } = parse_macro_input!(input);

    build_map(
        name,
        return_type.into(),
        pairs
            .into_pairs()
            .map(|kv| {
                let kv = kv.into_value();
                (kv.key.value(), Some(kv.value))
            })
            .collect(),
        false,
    )
}

#[proc_macro]
pub fn map_ignore_case(input: TokenStream) -> TokenStream {
    let BigMapInput {
        name,
        return_type,
        pairs,
    } = parse_macro_input!(input);

    build_map(
        name,
        return_type.into(),
        pairs
            .into_pairs()
            .map(|kv| {
                let kv = kv.into_value();
                (kv.key.value().to_lowercase(), Some(kv.value))
            })
            .collect(),
        true,
    )
}

#[proc_macro]
pub fn set(input: TokenStream) -> TokenStream {
    let SetInput { name, pairs } = parse_macro_input!(input);

    build_map(
        name,
        None,
        pairs
            .into_pairs()
            .map(|kv| (kv.into_value().key.value(), None))
            .collect(),
        false,
    )
}

#[proc_macro]
pub fn set_ignore_case(input: TokenStream) -> TokenStream {
    let SetInput { name, pairs } = parse_macro_input!(input);

    build_map(
        name,
        None,
        pairs
            .into_pairs()
            .map(|kv| (kv.into_value().key.value().to_lowercase(), None))
            .collect(),
        true,
    )
}

#[proc_macro]
pub fn tiny_map(input: TokenStream) -> TokenStream {
    let MapInput { name, pairs } = parse_macro_input!(input);

    build_tiny_map(
        name,
        pairs
            .iter()
            .map(|kv| (kv.key.value(), Some(&kv.value)))
            .collect::<HashMap<_, _>>(),
        false,
    )
}

#[proc_macro]
pub fn tiny_map_ignore_case(input: TokenStream) -> TokenStream {
    let MapInput { name, pairs } = parse_macro_input!(input);

    build_tiny_map(
        name,
        pairs
            .iter()
            .map(|kv| (kv.key.value().to_lowercase(), Some(&kv.value)))
            .collect::<HashMap<_, _>>(),
        true,
    )
}

#[proc_macro]
pub fn tiny_set(input: TokenStream) -> TokenStream {
    let SetInput { name, pairs } = parse_macro_input!(input);

    build_tiny_map(
        name,
        pairs
            .iter()
            .map(|kv| (kv.key.value(), None))
            .collect::<HashMap<_, _>>(),
        false,
    )
}

#[proc_macro]
pub fn tiny_set_ignore_case(input: TokenStream) -> TokenStream {
    let SetInput { name, pairs } = parse_macro_input!(input);

    build_tiny_map(
        name,
        pairs
            .iter()
            .map(|kv| (kv.key.value().to_lowercase(), None))
            .collect::<HashMap<_, _>>(),
        true,
    )
}
