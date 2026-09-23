/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

#![forbid(unsafe_code)]
#![deny(warnings)]

macro_rules! lookups {
    ($name:ident, [$($key:literal),* $(,)?]) => {
        mod $name {
            fn map(key: &[u8]) -> Option<&'static &'static str> {
                hashify::map!(key, &'static str, $($key => $key,)*)
            }

            fn map_ignore_case(key: &[u8]) -> Option<&'static &'static str> {
                hashify::map_ignore_case!(key, &'static str, $($key => $key,)*)
            }

            fn set(key: &[u8]) -> bool {
                hashify::set!(key, $($key,)*)
            }

            fn set_ignore_case(key: &[u8]) -> bool {
                hashify::set_ignore_case!(key, $($key,)*)
            }

            fn fnc_map(key: &[u8]) -> Option<&'static str> {
                hashify::fnc_map!(key, $($key => Some($key),)* _ => None)
            }

            fn fnc_map_ignore_case(key: &[u8]) -> Option<&'static str> {
                hashify::fnc_map_ignore_case!(key, $($key => Some($key),)* _ => None)
            }

            fn fnc_map_control_flow(words: &[&str]) -> (usize, usize) {
                let mut counts = (0, 0);
                for word in words {
                    hashify::fnc_map!(word.as_bytes(),
                        $($key => {
                            counts.0 += 1;
                            continue;
                        },)*
                        _ => if word.is_empty() {
                            break;
                        }
                    );
                    counts.1 += 1;
                }
                counts
            }

            fn fnc_map_ignore_case_control_flow(words: &[&str]) -> (usize, usize) {
                let mut counts = (0, 0);
                for word in words {
                    hashify::fnc_map_ignore_case!(word.as_bytes(),
                        $($key => {
                            counts.0 += 1;
                            continue;
                        },)*
                        _ => if word.is_empty() {
                            break;
                        }
                    );
                    counts.1 += 1;
                }
                counts
            }

            #[test]
            fn lookups() {
                let keys: &[&str] = &[$($key),*];
                for &key in keys {
                    let upper = key.to_ascii_uppercase();
                    assert_eq!(map(key.as_bytes()), Some(&key));
                    assert_eq!(map_ignore_case(upper.as_bytes()), Some(&key));
                    assert!(set(key.as_bytes()));
                    assert!(set_ignore_case(upper.as_bytes()));
                    assert_eq!(fnc_map(key.as_bytes()), Some(key));
                    assert_eq!(fnc_map_ignore_case(upper.as_bytes()), Some(key));
                }
                for miss in [&b"missing"[..], b"", b"a key that is not in any of the maps"] {
                    assert_eq!(map(miss), None);
                    assert_eq!(map_ignore_case(miss), None);
                    assert!(!set(miss));
                    assert!(!set_ignore_case(miss));
                    assert_eq!(fnc_map(miss), None);
                    assert_eq!(fnc_map_ignore_case(miss), None);
                }

                let mut words = keys.to_vec();
                words.extend(["missing", "", "after the break"]);
                assert_eq!(fnc_map_control_flow(&words), (keys.len(), 1));
                let upper: Vec<String> = words.iter().map(|word| word.to_ascii_uppercase()).collect();
                let upper: Vec<&str> = upper.iter().map(String::as_str).collect();
                assert_eq!(fnc_map_ignore_case_control_flow(&upper), (keys.len(), 1));
            }
        }
    };
}

lookups!(no_keys, []);

lookups!(one_key, ["only-key"]);

lookups!(
    sixteen_keys,
    [
        "key-00", "key-01", "key-02", "key-03", "key-04", "key-05", "key-06", "key-07", "key-08",
        "key-09", "key-10", "key-11", "key-12", "key-13", "key-14", "key-15",
    ]
);

lookups!(
    seventeen_keys,
    [
        "key-00",
        "key-01",
        "key-02",
        "key-03",
        "key-04",
        "key-05",
        "key-06",
        "key-07",
        "key-08",
        "key-09",
        "key-10",
        "key-11",
        "key-12",
        "key-13",
        "key-14",
        "key-15",
        "a key longer than sixteen bytes",
    ]
);

lookups!(
    sixty_four_keys,
    [
        "key-00",
        "key-01",
        "key-02",
        "key-03",
        "key-04",
        "key-05",
        "key-06",
        "key-07",
        "key-08",
        "key-09",
        "key-10",
        "key-11",
        "key-12",
        "key-13",
        "key-14",
        "key-15",
        "key-16",
        "key-17",
        "key-18",
        "key-19",
        "key-20",
        "key-21",
        "key-22",
        "key-23",
        "key-24",
        "key-25",
        "key-26",
        "key-27",
        "key-28",
        "key-29",
        "key-30",
        "key-31",
        "long key number 00 of the flat table",
        "long key number 01 of the flat table",
        "long key number 02 of the flat table",
        "long key number 03 of the flat table",
        "long key number 04 of the flat table",
        "long key number 05 of the flat table",
        "long key number 06 of the flat table",
        "long key number 07 of the flat table",
        "long key number 08 of the flat table",
        "long key number 09 of the flat table",
        "long key number 10 of the flat table",
        "long key number 11 of the flat table",
        "long key number 12 of the flat table",
        "long key number 13 of the flat table",
        "long key number 14 of the flat table",
        "long key number 15 of the flat table",
        "long key number 16 of the flat table",
        "long key number 17 of the flat table",
        "long key number 18 of the flat table",
        "long key number 19 of the flat table",
        "long key number 20 of the flat table",
        "long key number 21 of the flat table",
        "long key number 22 of the flat table",
        "long key number 23 of the flat table",
        "long key number 24 of the flat table",
        "long key number 25 of the flat table",
        "long key number 26 of the flat table",
        "long key number 27 of the flat table",
        "long key number 28 of the flat table",
        "long key number 29 of the flat table",
        "long key number 30 of the flat table",
        "long key number 31 of the flat table",
    ]
);

lookups!(
    sixty_five_keys,
    [
        "key-00", "key-01", "key-02", "key-03", "key-04", "key-05", "key-06", "key-07", "key-08",
        "key-09", "key-10", "key-11", "key-12", "key-13", "key-14", "key-15", "key-16", "key-17",
        "key-18", "key-19", "key-20", "key-21", "key-22", "key-23", "key-24", "key-25", "key-26",
        "key-27", "key-28", "key-29", "key-30", "key-31", "key-32", "key-33", "key-34", "key-35",
        "key-36", "key-37", "key-38", "key-39", "key-40", "key-41", "key-42", "key-43", "key-44",
        "key-45", "key-46", "key-47", "key-48", "key-49", "key-50", "key-51", "key-52", "key-53",
        "key-54", "key-55", "key-56", "key-57", "key-58", "key-59", "key-60", "key-61", "key-62",
        "key-63", "key-64",
    ]
);
