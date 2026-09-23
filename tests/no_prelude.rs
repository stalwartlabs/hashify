/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

#![no_implicit_prelude]
#![deny(warnings)]

extern crate hashify;
extern crate std;

macro_rules! lookups {
    ($name:ident, [$($key:literal),+ $(,)?]) => {
        mod $name {
            #![allow(non_camel_case_types, dead_code)]

            struct u8;
            struct u32;
            struct u64;
            struct u128;
            struct usize;

            fn map(
                key: &[::core::primitive::u8],
            ) -> ::core::option::Option<&'static &'static ::core::primitive::str> {
                ::hashify::map!(key, &'static ::core::primitive::str, $($key => $key),+)
            }

            fn map_ignore_case(
                key: &[::core::primitive::u8],
            ) -> ::core::option::Option<&'static &'static ::core::primitive::str> {
                ::hashify::map_ignore_case!(
                    key,
                    &'static ::core::primitive::str,
                    $($key => $key),+
                )
            }

            fn set(key: &[::core::primitive::u8]) -> ::core::primitive::bool {
                ::hashify::set!(key, $($key),+)
            }

            fn set_ignore_case(key: &[::core::primitive::u8]) -> ::core::primitive::bool {
                ::hashify::set_ignore_case!(key, $($key),+)
            }

            fn fnc_map(
                key: &[::core::primitive::u8],
            ) -> ::core::option::Option<&'static ::core::primitive::str> {
                ::hashify::fnc_map!(
                    key,
                    $($key => ::core::option::Option::Some($key),)+
                    _ => ::core::option::Option::None
                )
            }

            fn fnc_map_ignore_case(
                key: &[::core::primitive::u8],
            ) -> ::core::option::Option<&'static ::core::primitive::str> {
                ::hashify::fnc_map_ignore_case!(
                    key,
                    $($key => ::core::option::Option::Some($key),)+
                    _ => ::core::option::Option::None
                )
            }

            #[test]
            fn lookups_resolve_without_prelude() {
                for key in [$($key),+] {
                    let upper = key.to_ascii_uppercase();
                    ::std::assert_eq!(map(key.as_bytes()), ::core::option::Option::Some(&key));
                    ::std::assert_eq!(
                        map_ignore_case(upper.as_bytes()),
                        ::core::option::Option::Some(&key)
                    );
                    ::std::assert!(set(key.as_bytes()));
                    ::std::assert!(set_ignore_case(upper.as_bytes()));
                    ::std::assert_eq!(fnc_map(key.as_bytes()), ::core::option::Option::Some(key));
                    ::std::assert_eq!(
                        fnc_map_ignore_case(upper.as_bytes()),
                        ::core::option::Option::Some(key)
                    );
                }
                for miss in [&b""[..], b"missing", b"a key that is not in any of the maps"] {
                    ::std::assert_eq!(map(miss), ::core::option::Option::None);
                    ::std::assert_eq!(map_ignore_case(miss), ::core::option::Option::None);
                    ::std::assert!(!set(miss));
                    ::std::assert!(!set_ignore_case(miss));
                    ::std::assert_eq!(fnc_map(miss), ::core::option::Option::None);
                    ::std::assert_eq!(fnc_map_ignore_case(miss), ::core::option::Option::None);
                }
            }
        }
    };
}

lookups!(
    switch,
    ["get", "head", "post", "a long key of many bytes", "x",]
);

lookups!(
    flat,
    [
        "flat-00",
        "flat-01",
        "flat-02",
        "flat-03",
        "flat-04",
        "flat-05",
        "flat-06",
        "flat-07",
        "flat-08",
        "flat-09",
        "flat-10",
        "flat-11",
        "flat-12",
        "flat-13",
        "flat-14",
        "flat-15",
        "flat-16",
        "flat-17",
        "flat-18",
        "flat-19",
        "flat long key number 00",
        "flat long key number 01",
        "flat long key number 02",
    ]
);

lookups!(
    minimal_perfect_hash,
    [
        "s000",
        "s001",
        "s002",
        "s003",
        "s004",
        "s005",
        "s006",
        "s007",
        "s008",
        "s009",
        "s010",
        "s011",
        "s012",
        "s013",
        "s014",
        "s015",
        "s016",
        "s017",
        "s018",
        "s019",
        "s020",
        "s021",
        "s022",
        "s023",
        "s024",
        "s025",
        "s026",
        "s027",
        "s028",
        "s029",
        "s030",
        "s031",
        "s032",
        "s033",
        "s034",
        "s035",
        "s036",
        "s037",
        "s038",
        "s039",
        "s040",
        "s041",
        "s042",
        "s043",
        "s044",
        "s045",
        "s046",
        "s047",
        "s048",
        "s049",
        "s050",
        "s051",
        "s052",
        "s053",
        "s054",
        "s055",
        "s056",
        "s057",
        "s058",
        "s059",
        "s060",
        "s061",
        "s062",
        "s063",
        "s064",
        "long key number 000 of the minimal table",
        "long key number 001 of the minimal table",
        "long key number 002 of the minimal table",
        "long key number 003 of the minimal table",
        "long key number 004 of the minimal table",
        "long key number 005 of the minimal table",
        "long key number 006 of the minimal table",
        "long key number 007 of the minimal table",
        "long key number 008 of the minimal table",
        "long key number 009 of the minimal table",
        "long key number 010 of the minimal table",
        "long key number 011 of the minimal table",
        "long key number 012 of the minimal table",
        "long key number 013 of the minimal table",
        "long key number 014 of the minimal table",
        "long key number 015 of the minimal table",
        "long key number 016 of the minimal table",
        "long key number 017 of the minimal table",
        "long key number 018 of the minimal table",
        "long key number 019 of the minimal table",
        "long key number 020 of the minimal table",
        "long key number 021 of the minimal table",
        "long key number 022 of the minimal table",
        "long key number 023 of the minimal table",
        "long key number 024 of the minimal table",
        "long key number 025 of the minimal table",
        "long key number 026 of the minimal table",
        "long key number 027 of the minimal table",
        "long key number 028 of the minimal table",
        "long key number 029 of the minimal table",
        "long key number 030 of the minimal table",
        "long key number 031 of the minimal table",
        "long key number 032 of the minimal table",
        "long key number 033 of the minimal table",
        "long key number 034 of the minimal table",
        "long key number 035 of the minimal table",
        "long key number 036 of the minimal table",
        "long key number 037 of the minimal table",
        "long key number 038 of the minimal table",
        "long key number 039 of the minimal table",
        "long key number 040 of the minimal table",
        "long key number 041 of the minimal table",
        "long key number 042 of the minimal table",
        "long key number 043 of the minimal table",
        "long key number 044 of the minimal table",
        "long key number 045 of the minimal table",
        "long key number 046 of the minimal table",
        "long key number 047 of the minimal table",
        "long key number 048 of the minimal table",
        "long key number 049 of the minimal table",
        "long key number 050 of the minimal table",
        "long key number 051 of the minimal table",
        "long key number 052 of the minimal table",
        "long key number 053 of the minimal table",
        "long key number 054 of the minimal table",
        "long key number 055 of the minimal table",
        "long key number 056 of the minimal table",
        "long key number 057 of the minimal table",
        "long key number 058 of the minimal table",
        "long key number 059 of the minimal table",
        "long key number 060 of the minimal table",
        "long key number 061 of the minimal table",
        "long key number 062 of the minimal table",
        "long key number 063 of the minimal table",
        "long key number 064 of the minimal table",
    ]
);
