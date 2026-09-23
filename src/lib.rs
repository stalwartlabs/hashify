#![doc = include_str!("../README.md")]
/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

mod lookup;
use lookup::{Lookup, Payload};
use proc_macro::TokenStream;
use syn::punctuated::Punctuated;
use syn::{Error, ExprLit, Lit, UnOp};
use syn::{
    Expr, Result, Token, Type,
    parse::{Parse, ParseStream},
    parse_macro_input,
};

enum ParsedKey {
    Str(String),
    Binary(Vec<u8>),
    Char(char),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    Isize(isize),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    Usize(usize),
    Bool(bool),
}

struct MapInput {
    name: Expr,
    value_type: Type,
    pairs: Punctuated<KeyValue, Token![,]>,
}

struct FncMapInput {
    name: Expr,
    default: Expr,
    pairs: Punctuated<KeyValue, Token![,]>,
}

struct SetInput {
    name: Expr,
    keys: Punctuated<Key, Token![,]>,
}

impl Parse for MapInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let value_type: Type = input.parse()?;
        input.parse::<Token![,]>()?;
        let pairs = input.parse_terminated(KeyValue::parse, Token![,])?;
        Ok(MapInput {
            name,
            value_type,
            pairs,
        })
    }
}

impl Parse for FncMapInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Expr = input.parse()?;
        input.parse::<Token![,]>()?;

        let mut pairs = Punctuated::new();
        while !input.peek(Token![_]) {
            pairs.push_value(KeyValue::parse(input)?);
            if input.peek(Token![_]) {
                break;
            }
            pairs.push_punct(input.parse()?);
        }
        input.parse::<Token![_]>()?;
        input.parse::<Token![=>]>()?;
        let default: Expr = input.parse()?;
        if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
        }

        Ok(FncMapInput {
            name,
            default,
            pairs,
        })
    }
}

impl Parse for SetInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let keys = input.parse_terminated(Key::parse, Token![,])?;
        Ok(SetInput { name, keys })
    }
}

struct KeyValue {
    key: Key,
    value: Expr,
}

impl Parse for KeyValue {
    fn parse(input: ParseStream) -> Result<Self> {
        let key: Key = input.parse()?;
        input.parse::<Token![=>]>()?;
        let value = parse_expr(input)?;
        Ok(KeyValue { key, value })
    }
}

#[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Key {
    bytes: Vec<u8>,
}

impl Parse for Key {
    fn parse(input: ParseStream) -> Result<Self> {
        let key = parse_expr(input)?;
        let parsed = ParsedKey::from_expr(&key)
            .ok_or_else(|| Error::new_spanned(&key, "unsupported key expression"))?;

        Ok(Key {
            bytes: parsed.into_bytes(),
        })
    }
}

fn parse_expr(input: ParseStream) -> Result<Expr> {
    match input.cursor().literal() {
        Some((_, rest)) if rest.eof() || input.peek2(Token![,]) || input.peek2(Token![=>]) => {
            input.parse().map(Expr::Lit)
        }
        _ => input.parse(),
    }
}

fn expand<'x>(
    name: &Expr,
    keys: impl Iterator<Item = &'x Key>,
    payload: Payload<'_>,
    ignore_case: bool,
) -> TokenStream {
    let lowercase: Vec<Key>;
    let keys: Vec<&[u8]> = if ignore_case {
        lowercase = keys.map(Key::to_lowercase).collect();
        lowercase.iter().map(Key::as_bytes).collect()
    } else {
        keys.map(Key::as_bytes).collect()
    };
    Lookup::new(keys, payload, ignore_case)
        .map_or_else(|error| error, |lookup| lookup.expand(name))
        .into()
}

impl MapInput {
    fn expand(&self, ignore_case: bool) -> TokenStream {
        let payload = Payload::Value {
            ty: &self.value_type,
            values: self.pairs.iter().map(|pair| &pair.value).collect(),
        };
        expand(
            &self.name,
            self.pairs.iter().map(|pair| &pair.key),
            payload,
            ignore_case,
        )
    }
}

impl SetInput {
    fn expand(&self, ignore_case: bool) -> TokenStream {
        expand(&self.name, self.keys.iter(), Payload::Presence, ignore_case)
    }
}

impl FncMapInput {
    fn expand(&self, ignore_case: bool) -> TokenStream {
        let payload = Payload::Arms {
            arms: self.pairs.iter().map(|pair| &pair.value).collect(),
            default: &self.default,
        };
        expand(
            &self.name,
            self.pairs.iter().map(|pair| &pair.key),
            payload,
            ignore_case,
        )
    }
}

#[proc_macro]
pub fn map(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as MapInput).expand(false)
}

#[proc_macro]
pub fn map_ignore_case(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as MapInput).expand(true)
}

#[proc_macro]
pub fn set(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as SetInput).expand(false)
}

#[proc_macro]
pub fn set_ignore_case(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as SetInput).expand(true)
}

#[proc_macro]
pub fn fnc_map(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as FncMapInput).expand(false)
}

#[proc_macro]
pub fn fnc_map_ignore_case(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as FncMapInput).expand(true)
}

impl ParsedKey {
    // Credits to phf: https://github.com/rust-phf/rust-phf/blob/master/phf_macros/src/lib.rs
    fn from_expr(expr: &Expr) -> Option<ParsedKey> {
        match expr {
            Expr::Lit(lit) => match &lit.lit {
                Lit::Str(s) => Some(ParsedKey::Str(s.value())),
                Lit::ByteStr(s) => Some(ParsedKey::Binary(s.value())),
                Lit::Byte(s) => Some(ParsedKey::U8(s.value())),
                Lit::Char(s) => Some(ParsedKey::Char(s.value())),
                Lit::Int(s) => match s.suffix() {
                    // we've lost the sign at this point, so `-128i8` looks like `128i8`,
                    // which doesn't fit in an `i8`; parse it as a `u8` and cast (to `0i8`),
                    // which is handled below, by `Unary`
                    "i8" => Some(ParsedKey::I8(s.base10_parse::<u8>().ok()? as i8)),
                    "i16" => Some(ParsedKey::I16(s.base10_parse::<u16>().ok()? as i16)),
                    "i32" => Some(ParsedKey::I32(s.base10_parse::<u32>().ok()? as i32)),
                    "i64" => Some(ParsedKey::I64(s.base10_parse::<u64>().ok()? as i64)),
                    "i128" => Some(ParsedKey::I128(s.base10_parse::<u128>().ok()? as i128)),
                    "isize" => Some(ParsedKey::Isize(s.base10_parse::<usize>().ok()? as isize)),
                    "u8" => Some(ParsedKey::U8(s.base10_parse::<u8>().ok()?)),
                    "u16" => Some(ParsedKey::U16(s.base10_parse::<u16>().ok()?)),
                    "u32" => Some(ParsedKey::U32(s.base10_parse::<u32>().ok()?)),
                    "u64" => Some(ParsedKey::U64(s.base10_parse::<u64>().ok()?)),
                    "u128" => Some(ParsedKey::U128(s.base10_parse::<u128>().ok()?)),
                    "usize" => Some(ParsedKey::Usize(s.base10_parse::<usize>().ok()?)),
                    _ => None,
                },
                Lit::Bool(s) => Some(ParsedKey::Bool(s.value)),
                _ => None,
            },
            Expr::Array(array) => {
                let mut buf = vec![];
                for expr in &array.elems {
                    match expr {
                        Expr::Lit(lit) => match &lit.lit {
                            Lit::Int(s) => match s.suffix() {
                                "u8" | "" => buf.push(s.base10_parse::<u8>().ok()?),
                                _ => return None,
                            },
                            _ => return None,
                        },
                        _ => return None,
                    }
                }
                Some(ParsedKey::Binary(buf))
            }
            Expr::Unary(unary) => {
                // if we received an integer literal (always unsigned) greater than i__::max_value()
                // then casting it to a signed integer type of the same width will negate it to
                // the same absolute value so we don't need to negate it here
                macro_rules! try_negate (
                    ($val:expr) => {if $val < 0 { $val } else { -$val }}
                );

                match unary.op {
                    UnOp::Neg(_) => match ParsedKey::from_expr(&unary.expr)? {
                        ParsedKey::I8(v) => Some(ParsedKey::I8(try_negate!(v))),
                        ParsedKey::I16(v) => Some(ParsedKey::I16(try_negate!(v))),
                        ParsedKey::I32(v) => Some(ParsedKey::I32(try_negate!(v))),
                        ParsedKey::I64(v) => Some(ParsedKey::I64(try_negate!(v))),
                        ParsedKey::I128(v) => Some(ParsedKey::I128(try_negate!(v))),
                        ParsedKey::Isize(v) => Some(ParsedKey::Isize(try_negate!(v))),
                        _ => None,
                    },
                    UnOp::Deref(_) => {
                        let mut expr = &*unary.expr;
                        while let Expr::Group(group) = expr {
                            expr = &*group.expr;
                        }
                        match expr {
                            Expr::Lit(ExprLit {
                                lit: Lit::ByteStr(s),
                                ..
                            }) => Some(ParsedKey::Binary(s.value())),
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            Expr::Group(group) => ParsedKey::from_expr(&group.expr),
            _ => None,
        }
    }

    fn into_bytes(self) -> Vec<u8> {
        match self {
            ParsedKey::Str(s) => s.into_bytes(),
            ParsedKey::Binary(b) => b,
            ParsedKey::Char(c) => c.to_string().into_bytes(),
            ParsedKey::I8(i) => vec![i as u8],
            ParsedKey::I16(i) => i.to_be_bytes().to_vec(),
            ParsedKey::I32(i) => i.to_be_bytes().to_vec(),
            ParsedKey::I64(i) => i.to_be_bytes().to_vec(),
            ParsedKey::I128(i) => i.to_be_bytes().to_vec(),
            ParsedKey::Isize(i) => i.to_be_bytes().to_vec(),
            ParsedKey::U8(u) => vec![u],
            ParsedKey::U16(u) => u.to_be_bytes().to_vec(),
            ParsedKey::U32(u) => u.to_be_bytes().to_vec(),
            ParsedKey::U64(u) => u.to_be_bytes().to_vec(),
            ParsedKey::U128(u) => u.to_be_bytes().to_vec(),
            ParsedKey::Usize(u) => u.to_be_bytes().to_vec(),
            ParsedKey::Bool(b) => vec![b as u8],
        }
    }
}

impl Key {
    fn to_lowercase(&self) -> Key {
        Key {
            bytes: self.bytes.to_ascii_lowercase(),
        }
    }

    fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}
