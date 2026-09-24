/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

mod keys;

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

#[proc_macro]
pub fn generate(input: TokenStream) -> TokenStream {
    let tokens: Vec<TokenTree> = input.into_iter().collect();
    let [
        TokenTree::Ident(callback),
        _,
        TokenTree::Ident(name),
        _,
        TokenTree::Literal(count),
    ] = tokens.as_slice()
    else {
        panic!("expected `callback, name, count`");
    };
    let count: usize = count
        .to_string()
        .replace('_', "")
        .parse()
        .expect("count is an integer literal");

    let entries = keys::generate(count)
        .into_iter()
        .enumerate()
        .flat_map(|(idx, key)| {
            [
                TokenTree::Literal(Literal::string(&key)),
                TokenTree::Punct(Punct::new('=', Spacing::Joint)),
                TokenTree::Punct(Punct::new('>', Spacing::Alone)),
                TokenTree::Literal(Literal::usize_unsuffixed(idx)),
                TokenTree::Punct(Punct::new(',', Spacing::Alone)),
            ]
        });
    let body = [
        TokenTree::Ident(name.clone()),
        TokenTree::Punct(Punct::new(':', Spacing::Alone)),
        TokenTree::Ident(Ident::new("u32", Span::call_site())),
        TokenTree::Punct(Punct::new(',', Spacing::Alone)),
    ]
    .into_iter()
    .chain(entries)
    .collect();

    [
        TokenTree::Ident(callback.clone()),
        TokenTree::Punct(Punct::new('!', Spacing::Alone)),
        TokenTree::Group(Group::new(Delimiter::Brace, body)),
    ]
    .into_iter()
    .collect()
}
