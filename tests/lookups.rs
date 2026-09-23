/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use std::collections::HashMap;
use std::fmt::Debug;

const LONG_KEY_A: &[u8] = b"0123456789abcdef0123456789abcdefXYZ";
const LONG_KEY_B: &[u8] = b"0123456789abcdef0123456789abcdefXYz";

fn probes(keys: &[&[u8]]) -> Vec<Vec<u8>> {
    let mut probes: Vec<Vec<u8>> = Vec::new();
    for key in keys {
        probes.push(key.to_vec());
        probes.push(key.to_ascii_uppercase());
        probes.push(key.to_ascii_lowercase());
        probes.push([key, &b"x"[..]].concat());
        probes.push([&b"x"[..], key].concat());
        probes.push([key, &[0u8][..]].concat());
        if let Some((_, rest)) = key.split_first() {
            probes.push(rest.to_vec());
        }
        if let Some((_, rest)) = key.split_last() {
            probes.push(rest.to_vec());
        }
        for pos in 0..key.len() {
            for mask in [0x01u8, 0x20, 0x80, 0xff] {
                let mut probe = key.to_vec();
                probe[pos] ^= mask;
                probes.push(probe);
            }
        }
    }
    let mut state = 0x2545_f491_4f6c_dd1du64;
    for len in 0..=48 {
        for _ in 0..64 {
            probes.push(
                (0..len)
                    .map(|_| {
                        state ^= state << 13;
                        state ^= state >> 7;
                        state ^= state << 17;
                        b"aAbBcCxyz019_ \x00\xff\xc1\xc9\xda\xe1\xe9\xfa"[(state % 22) as usize]
                    })
                    .collect(),
            );
        }
    }
    probes
}

fn check<V: Copy + PartialEq + Debug>(
    pairs: &[(&[u8], V)],
    ignore_case: bool,
    lookup: impl Fn(&[u8]) -> Option<V>,
) {
    let normalize = |key: &[u8]| {
        if ignore_case {
            key.to_ascii_lowercase()
        } else {
            key.to_vec()
        }
    };
    let reference: HashMap<Vec<u8>, V> = pairs
        .iter()
        .map(|(key, value)| (normalize(key), *value))
        .collect();
    assert_eq!(reference.len(), pairs.len(), "test pairs must be unique");
    let keys: Vec<&[u8]> = pairs.iter().map(|(key, _)| *key).collect();
    for probe in probes(&keys) {
        assert_eq!(
            lookup(&probe),
            reference.get(&normalize(&probe)).copied(),
            "lookup mismatch for {:?}",
            String::from_utf8_lossy(&probe)
        );
    }
}

macro_rules! pairs {
    ($($key:expr => $value:expr),* $(,)?) => {
        [$(($key as &[u8], $value)),*]
    };
}

#[test]
fn map_all_length_classes() {
    fn lookup(key: &[u8]) -> Option<u32> {
        hashify::map! { key, u32,
            b"" => 0,
            b"a" => 1,
            b"b" => 2,
            b"ab" => 3,
            b"ba" => 4,
            b"abc" => 5,
            b"abd" => 6,
            b"abcd" => 7,
            b"abce" => 8,
            b"abcde" => 9,
            b"abcdef" => 10,
            b"abcdefg" => 11,
            b"abcdefgh" => 12,
            b"abcdefghi" => 13,
            b"aaaaaaaa" => 14,
            b"aaaaaaaaa" => 15,
            b"aaaaaaaaaa" => 16,
            b"aaaaaaaaaaaaaaa" => 17,
            b"aaaaaaaaaaaaaaaa" => 18,
            b"aaaaaaaaaaaaaaaaa" => 19,
            b"0123456789abcdef" => 20,
            b"0123456789abcdefg" => 21,
            b"0123456789abcdefgh" => 22,
            b"0123456789abcdef01234567" => 23,
            b"0123456789abcdef0123456789abcde" => 24,
            b"0123456789abcdef0123456789abcdef" => 25,
            b"0123456789abcdef0123456789abcdefXYZ" => 26,
            b"0123456789abcdef0123456789abcdefXYz" => 27,
            b"\x00" => 28,
            b"\x00\x00" => 29,
            b"\x00\x00\x00\x00" => 30,
            b"\x00\x00\x00\x00\x00\x00\x00\x00" => 31,
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00" => 32,
            b"\xff\xff\xff\xff\xff" => 33,
            b"\x00abc" => 34,
            b"abc\x00" => 35,
            [1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70] => 36,
        }
        .copied()
    }

    let long: Vec<u8> = (1..=70).collect();
    let pairs = pairs! {
        b"" => 0, b"a" => 1, b"b" => 2, b"ab" => 3, b"ba" => 4, b"abc" => 5, b"abd" => 6,
        b"abcd" => 7, b"abce" => 8, b"abcde" => 9, b"abcdef" => 10, b"abcdefg" => 11,
        b"abcdefgh" => 12, b"abcdefghi" => 13, b"aaaaaaaa" => 14, b"aaaaaaaaa" => 15,
        b"aaaaaaaaaa" => 16, b"aaaaaaaaaaaaaaa" => 17, b"aaaaaaaaaaaaaaaa" => 18,
        b"aaaaaaaaaaaaaaaaa" => 19, b"0123456789abcdef" => 20, b"0123456789abcdefg" => 21,
        b"0123456789abcdefgh" => 22, b"0123456789abcdef01234567" => 23,
        b"0123456789abcdef0123456789abcde" => 24, b"0123456789abcdef0123456789abcdef" => 25,
        LONG_KEY_A => 26, LONG_KEY_B => 27, b"\x00" => 28, b"\x00\x00" => 29,
        b"\x00\x00\x00\x00" => 30, b"\x00\x00\x00\x00\x00\x00\x00\x00" => 31,
        b"\x00\x00\x00\x00\x00\x00\x00\x00\x00" => 32, b"\xff\xff\xff\xff\xff" => 33,
        b"\x00abc" => 34, b"abc\x00" => 35, &long => 36,
    };
    check(&pairs, false, lookup);
}

#[test]
fn map_ignore_case_all_length_classes() {
    fn lookup(key: &[u8]) -> Option<u32> {
        hashify::map_ignore_case! { key, u32,
            "A" => 1,
            "Bc" => 2,
            "DEF" => 3,
            "GhIj" => 4,
            "KLMNOPQ" => 5,
            "rStUvWxY" => 6,
            "Content-Type" => 7,
            "X-Forwarded-For!" => 8,
            "Strict-Transport-Security" => 9,
            "\u{c9}t\u{c9}" => 10,
            "\u{e9}t\u{e9}" => 11,
            "@[`{" => 12,
            "0123456789ABCDEF0123456789abcdefXYZ" => 13,
            "Z" => 14,
            "_" => 15,
        }
        .copied()
    }

    let pairs = pairs! {
        b"A" => 1, b"Bc" => 2, b"DEF" => 3, b"GhIj" => 4, b"KLMNOPQ" => 5, b"rStUvWxY" => 6,
        b"Content-Type" => 7, b"X-Forwarded-For!" => 8, b"Strict-Transport-Security" => 9,
        "\u{c9}t\u{c9}".as_bytes() => 10, "\u{e9}t\u{e9}".as_bytes() => 11, b"@[`{" => 12,
        b"0123456789ABCDEF0123456789abcdefXYZ" => 13, b"Z" => 14, b"_" => 15,
    };
    check(&pairs, true, lookup);
}

#[test]
fn map_ignore_case_all_length_classes_hashed() {
    fn lookup(key: &[u8]) -> Option<u32> {
        hashify::map_ignore_case! { key, u32,
            "A" => 1,
            "Bc" => 2,
            "DEF" => 3,
            "GhIj" => 4,
            "KLMNOPQ" => 5,
            "rStUvWxY" => 6,
            "Content-Type" => 7,
            "X-Forwarded-For!" => 8,
            "Strict-Transport-Security" => 9,
            "\u{c9}t\u{c9}" => 10,
            "\u{e9}t\u{e9}" => 11,
            "@[`{" => 12,
            "0123456789ABCDEF0123456789abcdefXYZ" => 13,
            "Z" => 14,
            "_" => 15,
            "\u{c9}" => 16,
            "\u{e9}\u{c9}\u{da}" => 17,
            "\u{441}\u{442}\u{43e}\u{43f}" => 18,
            "\u{56de}\u{590d}" => 19,
            "?@AZ[\\]^`az{" => 20,
            "\u{dc}n\u{ef}c\u{f6}d\u{e9}-Header" => 21,
            "Long-\u{dc}n\u{ef}c\u{f6}d\u{e9}-Header-Name" => 22,
            b"\xc1\xda\xe1\xfa" => 23,
            b"\xc9\xe9\xc9\xe9\xc9\xe9\xc9\xe9\xc9" => 24,
            b"\xe9" => 25,
            b"x\xda" => 26,
            b"Long-Raw-Bytes-\xc1\xc9\xda\xe1\xe9\xfa" => 27,
        }
        .copied()
    }

    let pairs = pairs! {
        b"A" => 1, b"Bc" => 2, b"DEF" => 3, b"GhIj" => 4, b"KLMNOPQ" => 5, b"rStUvWxY" => 6,
        b"Content-Type" => 7, b"X-Forwarded-For!" => 8, b"Strict-Transport-Security" => 9,
        "\u{c9}t\u{c9}".as_bytes() => 10, "\u{e9}t\u{e9}".as_bytes() => 11, b"@[`{" => 12,
        b"0123456789ABCDEF0123456789abcdefXYZ" => 13, b"Z" => 14, b"_" => 15,
        "\u{c9}".as_bytes() => 16, "\u{e9}\u{c9}\u{da}".as_bytes() => 17,
        "\u{441}\u{442}\u{43e}\u{43f}".as_bytes() => 18, "\u{56de}\u{590d}".as_bytes() => 19,
        b"?@AZ[\\]^`az{" => 20, "\u{dc}n\u{ef}c\u{f6}d\u{e9}-Header".as_bytes() => 21,
        "Long-\u{dc}n\u{ef}c\u{f6}d\u{e9}-Header-Name".as_bytes() => 22,
        b"\xc1\xda\xe1\xfa" => 23, b"\xc9\xe9\xc9\xe9\xc9\xe9\xc9\xe9\xc9" => 24, b"\xe9" => 25,
        b"x\xda" => 26, b"Long-Raw-Bytes-\xc1\xc9\xda\xe1\xe9\xfa" => 27,
    };
    check(&pairs, true, lookup);
}

#[test]
fn sets_all_length_classes() {
    fn contains(key: &[u8]) -> bool {
        hashify::set! { key,
            "", "a", "ab", "abc", "abcd", "abcdefg", "abcdefgh", "abcdefghijklmnop",
            "abcdefghijklmnopq", "0123456789abcdef0123456789abcdefXYZ",
        }
    }
    fn contains_ignore_case(key: &[u8]) -> bool {
        hashify::set_ignore_case! { key,
            "A", "aB", "ABC", "AbCd", "ABCDEFG", "ABCDEFGH", "ABCDEFGHIJKLMNOP",
            "ABCDEFGHIJKLMNOPQ", "0123456789ABCDEF0123456789ABCDEFxyz",
        }
    }

    let keys = pairs! {
        b"" => true, b"a" => true, b"ab" => true, b"abc" => true, b"abcd" => true,
        b"abcdefg" => true, b"abcdefgh" => true, b"abcdefghijklmnop" => true,
        b"abcdefghijklmnopq" => true, b"0123456789abcdef0123456789abcdefXYZ" => true,
    };
    check(&keys, false, |key| contains(key).then_some(true));
    check(&keys[1..], true, |key| {
        contains_ignore_case(key).then_some(true)
    });
}

#[test]
fn maps_with_a_single_length_class() {
    fn narrow(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8, "x" => 1, "yz" => 2, "abc" => 3, }.copied()
    }
    fn medium(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8, "abcd" => 1, "abcde" => 2, "abcdefg" => 3, }.copied()
    }
    fn wide(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8, "abcdefgh" => 1, "abcdefghi" => 2, "abcdefghijklmnop" => 3, }
            .copied()
    }
    fn long(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8, "abcdefghijklmnopq" => 1, "abcdefghijklmnopqrstuvwxyz" => 2, }
            .copied()
    }
    fn single(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8, "only" => 1, }.copied()
    }
    fn empty(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8, "" => 1, }.copied()
    }

    check(
        &pairs! { b"x" => 1, b"yz" => 2, b"abc" => 3 },
        false,
        narrow,
    );
    check(
        &pairs! { b"abcd" => 1, b"abcde" => 2, b"abcdefg" => 3 },
        false,
        medium,
    );
    check(
        &pairs! { b"abcdefgh" => 1, b"abcdefghi" => 2, b"abcdefghijklmnop" => 3 },
        false,
        wide,
    );
    check(
        &pairs! { b"abcdefghijklmnopq" => 1, b"abcdefghijklmnopqrstuvwxyz" => 2 },
        false,
        long,
    );
    check(&pairs! { b"only" => 1 }, false, single);
    check(&pairs! { b"" => 1 }, false, empty);
}

#[test]
fn map_accepts_owned_and_array_keys() {
    fn lookup_vec(key: Vec<u8>) -> Option<u8> {
        hashify::map! { key, u8, "abc" => 1, "defghijk" => 2, }.copied()
    }
    fn lookup_array(key: &[u8; 16]) -> Option<u8> {
        hashify::map! { key, u8, "abcdefghijklmnop" => 1, "defghijk" => 2, }.copied()
    }

    assert_eq!(lookup_vec(b"abc".to_vec()), Some(1));
    assert_eq!(lookup_vec(b"defghijk".to_vec()), Some(2));
    assert_eq!(lookup_vec(b"xyz".to_vec()), None);
    assert_eq!(lookup_array(b"abcdefghijklmnop"), Some(1));
    assert_eq!(lookup_array(b"abcdefghijklmnoq"), None);
}

#[test]
fn keys_sharing_canonical_words_differ_by_length() {
    fn lookup(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8,
            "aaaa" => 4,
            "aaaaaa" => 6,
            "aaaaaaaa" => 8,
            "aaaaaaaaaa" => 10,
            "aaaaaaaaaaaa" => 12,
            "aaaaaaaaaaaaaa" => 14,
            "aaaaaaaaaaaaaaaa" => 16,
        }
        .copied()
    }

    for len in 0u8..=40 {
        let expected = ((4..=16).contains(&len) && len % 2 == 0).then_some(len);
        assert_eq!(
            lookup(&vec![b'a'; usize::from(len)]),
            expected,
            "length {len}"
        );
    }
}

#[test]
fn keys_sharing_canonical_words_differ_by_length_hashed() {
    fn lookup(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8,
            "aaaa" => 4,
            "aaaaaa" => 6,
            "aaaaaaaa" => 8,
            "aaaaaaaaaa" => 10,
            "aaaaaaaaaaaa" => 12,
            "aaaaaaaaaaaaaa" => 14,
            "aaaaaaaaaaaaaaaa" => 16,
            "" => 20,
            "\0" => 21,
            "\0\0" => 22,
            "\0\0\0" => 23,
            "\0\0\0\0" => 24,
            "\0\0\0\0\0\0\0\0" => 25,
            "\0\0\0\0\0\0\0\0\0" => 26,
            "abab" => 27,
            "ababab" => 28,
            "of" => 29,
            "off" => 30,
            "i" => 31,
            "ii" => 32,
            "iii" => 33,
        }
        .copied()
    }

    let pairs = pairs! {
        b"aaaa" => 4, b"aaaaaa" => 6, b"aaaaaaaa" => 8, b"aaaaaaaaaa" => 10,
        b"aaaaaaaaaaaa" => 12, b"aaaaaaaaaaaaaa" => 14, b"aaaaaaaaaaaaaaaa" => 16, b"" => 20,
        b"\0" => 21, b"\0\0" => 22, b"\0\0\0" => 23, b"\0\0\0\0" => 24,
        b"\0\0\0\0\0\0\0\0" => 25, b"\0\0\0\0\0\0\0\0\0" => 26, b"abab" => 27, b"ababab" => 28,
        b"of" => 29, b"off" => 30, b"i" => 31, b"ii" => 32, b"iii" => 33,
    };
    check(&pairs, false, lookup);
    let reference: HashMap<&[u8], u8> = pairs.iter().copied().collect();
    for len in 0..=40 {
        for byte in [b'a', 0, b'i', b'f'] {
            let key = vec![byte; len];
            assert_eq!(
                lookup(&key),
                reference.get(key.as_slice()).copied(),
                "{len} bytes of {byte}"
            );
        }
    }
}

fn checked(fail: bool) -> Result<u32, u32> {
    if fail { Err(7) } else { Ok(3) }
}

macro_rules! control_flow_tests {
    ($name:ident, [$($filler:literal),* $(,)?]) => {
        #[test]
        fn $name() {
            fn arms(words: &[&str], fail: bool) -> Result<Vec<u32>, u32> {
                let mut out = Vec::new();
                for word in words {
                    hashify::fnc_map! { word.as_bytes(),
                        "stop" => break,
                        "skip" => continue,
                        "exit" => return Ok(Vec::new()),
                        "check" => out.push(checked(fail)?),
                        "block" => {
                            out.push(4);
                            out.push(5);
                        },
                        $($filler => out.push(1),)*
                        _ => out.push(0)
                    }
                    out.push(9);
                }
                Ok(out)
            }

            fn default_arm(words: &[&str], fail: bool) -> Result<Vec<u32>, u32> {
                let mut out = Vec::new();
                for word in words {
                    hashify::fnc_map_ignore_case! { word.as_bytes(),
                        "stop" => out.push(1),
                        "skip" => out.push(2),
                        "exit" => out.push(3),
                        "check" => out.push(4),
                        "block" => out.push(5),
                        $($filler => out.push(6),)*
                        _ => match word.len() {
                            0 => break,
                            1 => continue,
                            2 => return Ok(Vec::new()),
                            _ => out.push(checked(fail)?),
                        }
                    }
                    out.push(9);
                }
                Ok(out)
            }

            fn bare_default(words: &[&str]) -> Vec<u32> {
                let mut out = Vec::new();
                for word in words {
                    hashify::fnc_map! { word.as_bytes(),
                        "stop" => break,
                        "skip" => out.push(2),
                        "exit" => out.push(3),
                        "check" => out.push(4),
                        "block" => out.push(5),
                        $($filler => out.push(6),)*
                        _ => continue
                    }
                    out.push(9);
                }
                out
            }

            fn assign(word: &str) -> u32 {
                let value;
                hashify::fnc_map! { word.as_bytes(),
                    "stop" => { value = 1; },
                    "skip" => { value = 2; },
                    "exit" => { value = 3; },
                    "check" => { value = 4; },
                    "block" => { value = 5; },
                    $($filler => { value = 6; },)*
                    _ => { value = 0; }
                }
                value
            }

            assert_eq!(
                arms(&["x", "block", "skip", "check", "stop", "x"], false),
                Ok(vec![0, 9, 4, 5, 9, 3, 9])
            );
            assert_eq!(arms(&["x", "check", "x"], true), Err(7));
            assert_eq!(arms(&["block", "exit", "block"], false), Ok(Vec::new()));
            assert_eq!(arms(&["STOP", "Skip"], false), Ok(vec![0, 9, 0, 9]));

            assert_eq!(
                default_arm(&["STOP", "x", "SKIP", "xyz", "", "check"], false),
                Ok(vec![1, 9, 2, 9, 3, 9])
            );
            assert_eq!(default_arm(&["Block", "xyz"], true), Err(7));
            assert_eq!(default_arm(&["exit", "xy", "exit"], false), Ok(Vec::new()));

            assert_eq!(
                bare_default(&["x", "skip", "y", "block", "stop", "exit"]),
                vec![2, 9, 5, 9]
            );

            assert_eq!(assign("block"), 5);
            assert_eq!(assign("stop"), 1);
            assert_eq!(assign("Block"), 0);
            assert_eq!(assign(""), 0);

            let fillers: &[&str] = &[$($filler),*];
            for &filler in fillers {
                assert_eq!(arms(&[filler], false), Ok(vec![1, 9]));
                assert_eq!(default_arm(&[filler], false), Ok(vec![6, 9]));
                assert_eq!(bare_default(&[filler, "x", filler]), vec![6, 9, 6, 9]);
                assert_eq!(assign(filler), 6);
            }
        }
    };
}

control_flow_tests!(fnc_map_control_flow_switch, ["filler-a", "filler-b"]);

control_flow_tests!(
    fnc_map_control_flow_hashed,
    [
        "filler-01",
        "filler-02",
        "filler-03",
        "filler-04",
        "filler-05",
        "filler-06",
        "filler-07",
        "filler-08",
        "filler-09",
        "filler-10",
        "filler-11",
        "filler-12",
        "filler-13",
        "a filler key longer than sixteen bytes",
    ]
);

macro_rules! strategy_tests {
    ($name:ident, [$($key:literal),* $(,)?]) => {
        #[test]
        fn $name() {
            fn map(key: &[u8]) -> Option<&'static str> {
                hashify::map! { key, &'static str, $($key => $key),* }.copied()
            }
            fn map_ignore_case(key: &[u8]) -> Option<&'static str> {
                hashify::map_ignore_case! { key, &'static str, $($key => $key),* }.copied()
            }
            fn set(key: &[u8]) -> Option<bool> {
                hashify::set! { key, $($key),* }.then_some(true)
            }
            fn set_ignore_case(key: &[u8]) -> Option<bool> {
                hashify::set_ignore_case! { key, $($key),* }.then_some(true)
            }
            fn fnc_map(key: &[u8]) -> Option<&'static str> {
                hashify::fnc_map! { key, $($key => Some($key),)* _ => None }
            }
            fn fnc_map_ignore_case(key: &[u8]) -> Option<&'static str> {
                hashify::fnc_map_ignore_case! { key, $($key => Some($key),)* _ => None }
            }

            let values = [$(($key.as_bytes(), $key)),*];
            let present = [$(($key.as_bytes(), true)),*];
            check(&values, false, map);
            check(&values, true, map_ignore_case);
            check(&present, false, set);
            check(&present, true, set_ignore_case);
            check(&values, false, fnc_map);
            check(&values, true, fnc_map_ignore_case);
        }
    };
}

strategy_tests!(
    switch_strategy,
    [
        "-4mts934z9c2pz_l",
        "2x87",
        "2y",
        "3b2ct99zkk4oa",
        "3by-a0ro9",
        "3w_wa66",
        "7oz4w8w1r7ay4i57",
        "bbb6ayn-b5o037owoo1sb_7glsh",
        "f04gk5",
        "q",
    ]
);

strategy_tests!(
    flat_strategy,
    [
        "-2q",
        "-cdxxlpb",
        "02fluy",
        "0_5x9",
        "0eqf9oxq-r5ajcy_kh4fpggb",
        "0i59z34u",
        "1iwzhqhhfvzngb",
        "1newa",
        "2x7vfo6",
        "3i26tequtvtz",
        "4ftco17o5r",
        "4nz5",
        "4w11w8713oukr2tt47549_tn34xevamgd",
        "59lg2xb5hxsxtb",
        "6",
        "b",
        "b7idqcikkg1o4c",
        "c3sw1jxr252_3sz",
        "cisyov0l5shj6-gv5p4qkk1pzw8j10bylz4d2r",
        "e93v1r41bfwlzqidk3y1sjas71axc6y80n",
        "ef",
        "ffxktqnc9k-z4x604r",
        "ggtmb0d_31n9ea",
        "gnb51",
        "h",
        "j",
        "kz15p3r",
        "l5ay9",
        "nn--4b9",
        "nrukgp2mxlwiior7yzvr49uzs6extz2",
        "q7-f98g",
        "qq",
        "r9og5irp",
        "teo3mh",
        "whsv3bt07cqzj2ofu",
        "x",
        "x1uy-5k7lpobluli4",
        "xnuwev1xk30s1i",
        "y7mr99m3i",
        "yau151lgbzn8yn",
    ]
);

strategy_tests!(
    minimal_perfect_hash_strategy,
    [
        "0l1cqxx",
        "0tqp3_qvc",
        "12tle",
        "197b2ezc1op",
        "19rbu",
        "1bpn6r9e-o-ibux7qh1h5ygu86g9a2",
        "1wwr3b9dbxq1t",
        "2dw",
        "2jzjkg32509lirmj",
        "2wrk4y3",
        "35t2bm",
        "4tpb56_dhv",
        "4w",
        "6hkp",
        "6m",
        "7",
        "7v",
        "8l",
        "8lrvfw9i_s5r1w_s_8_c_jma24-",
        "8ui5c",
        "9id",
        "9tfc845pg7g7",
        "_emk",
        "_k_89",
        "_y",
        "a",
        "a38zdrpr55",
        "b",
        "bz0u",
        "c-dx3u_",
        "c15s6voe9sh",
        "c40h8sji1fd",
        "c4m-8da2",
        "c5",
        "cmnr3-c",
        "e6-n3tb",
        "enj3syxk-t1256oxssb1xwtp5aai5j6",
        "f",
        "fcfvnem-o3",
        "g4r-pt-q5t7va_9u",
        "g5xx0sqgv865",
        "go3l51mm",
        "gupdd01vx",
        "h0",
        "h3irrg-exc430mtw",
        "h6a1tevwm3e",
        "hfqscw09v",
        "hr",
        "i9jzm65k8lmqxs",
        "ihk0",
        "j9ahosno74_4u6m1lfchbgmqfg1zog3wz0hs0",
        "jbs-_hccy9v7r4",
        "jr9gh8hlm",
        "k",
        "k9z4",
        "lp1zqxzw7_f",
        "lx1hg7jv_7",
        "lxluxqtygb8it",
        "ly7wlx_",
        "m",
        "m2v2wcytzfsl_",
        "m_sqjcvu",
        "n93z",
        "nqpmqilcq",
        "o0kfvn80rohc5",
        "o4e",
        "o6s_99rntbr2y",
        "pgy2m",
        "pi_4v7irbkcb3d1154_x5kslei7g_w01rq0",
        "pu2j_2",
        "pul-gg",
        "pzcz",
        "q",
        "q7om2672zjoj5yaek9ctbr2y-z80ixgc",
        "qmv-hi7ayf8lc",
        "rp4",
        "sjg0t",
        "t3p7rbv",
        "t_4y8w69_9ovbrku688gn8rshe22fw",
        "taeg",
        "uadichd",
        "ufd-f9agbfbk4",
        "ukuewyy",
        "ul-f",
        "v-",
        "v8th0fnpd",
        "vd",
        "vhbh",
        "vuvw",
        "wgrrydi",
        "whds",
        "wx7c3lp",
        "x-e5npwdvp-0fqnuknn16_xm_2_29csblgbjs4",
        "x29ea",
        "y",
        "yy15y",
        "z",
        "z06ew3",
        "zoanqx",
        "zudrncu",
    ]
);

strategy_tests!(
    minimal_perfect_hash_long_keys_strategy,
    [
        "-qltevz0l2-czmnv4tyfzj5yove89a8ipemm4wf",
        "0067n14_vl4pjbtzodvs782zoqpyhwwf3",
        "02vex2c7haq2ftv66kc7fsqar_a75y90_u",
        "0o2mrdk1b66yp3acr1phg77jk8",
        "0u3vja9_fe6yrgtew0-zc__xj-t65k86bh_xdgvcs-ys",
        "1-pygplfbvpzr8wfuoa",
        "12mbc5mg9lhnjm6kqtfsen-puuohmk0vj",
        "1_1g98c7e7ahrsc33xzdql3-qn4w6cwhe",
        "1krivf_4o6elki65xc8dbt077sphr",
        "2olh98cymtik_ixyhzwg9skam72pgf461d4p",
        "41gz87zj7yjkbtou1ijzsw345gqxk5nufaw",
        "4slvshurm7dni2iyxmb31p53te30u59jx2",
        "5grava4rwv5f59pmnfuaxul8ufpdpoxcyc6371",
        "6xlsfbx4yjr2o_1p60butsx1jykan8kwgb1k2ab63n9jdu7",
        "84b0gdnsyfhknaz80uujfy85wkrzb5ait81mso",
        "8zn5a14vks7ruruv79d",
        "9k20z7m0jj6dh6u2hhjieikxvix0de0_f-wjpgw7tynjfcg",
        "9rf_svesr8_z_0_zbv56809osh2p-t",
        "_d5mrbu2y5s0qxg4f3va4fx0h1t0zk30q125",
        "adpt1jf88yt9eo278rqvwefb",
        "aflkrhu2k18husj7bhuxta2r9",
        "bag60n8wysijsghhn4bo1j7txi",
        "c35g60v640myzml0ygjroqdry51uj2ujubkyjtko",
        "cks60xd5by-7v506um3a97-va9-u0w",
        "d7mbddvyc4wn5vl5ua8b5743fk5i3spd2k9t05w0zl",
        "eq9qvc44ihhrafqwasq0ytwxa-2wgo0t_dil3",
        "f9tq4czn8qzx3r_pq797e_2y877n",
        "gggy4cpms5-53kwv7--kkn31_zbhaf5lb0x6-",
        "hhz5q7tg56npr0xfdgm_o3tld4o",
        "hsmlhungqdv08_p4fyqd3f86",
        "ifpter8g4v5bsiqutj-6_vo64s4f9sy",
        "ih0-dfsisa2-e-kqrug7pkkqjpk3",
        "isvigfrq4ycj2e7y4ntewysrfdbhcq",
        "jl2629e0mp_qpzkfpe882qub-s7s-na_4d",
        "jmzdsoyou88pjtt8umujo",
        "kcpc8rwlza_74co8s660a",
        "ktz8tcwdee1_ywr2_bryvrnl2",
        "l8ppk_ev_vvqmao0csnc1153zxg3z9ji1",
        "lei3g9-e5fa1q-04wmng019dbf66t",
        "ly6uly5srj6yf20g7_g7rxzwvap__p1g26554ewk80f6ky",
        "mamd2w8ch-37p_kb8pbd2vhxgw",
        "mnftlvgx1fyzevnl39xsabwh0cnm8fui7hqrx8x5",
        "mukj-r5c8wom0329l_80-ywg8kobgy",
        "nav-d1mmgxyl907wzt68s7h1l2i",
        "o7hukug06n1bf9zbnons6sigm59rmsfwgsk0d0o2mvetpw8",
        "ol77oicq49znhvwvmn949k4h2xj42iwhsx4a5c",
        "op653akbhcyacasrudsuycqt",
        "p14eccreh-_w1l_as_26cjq-zv7e35t3",
        "psxp05nbc7n7_d5fdvob9xvam9y7v-0jqgt66vd",
        "qij9a64obqj_s-x5kenv5aku4",
        "r-wn-_35ce-yq_ljy1dxa6020gyz64efqcwdxhuv0g5bz1",
        "tg-5wil6s_h1ugdk7",
        "tjvyo6tkj2r_2kosq9q1",
        "tn00_yuhpf8b-18vva",
        "tquyacwjvfiyzvojpi-p8qm6fes",
        "u06q4e703c2n7qfikirdxdd-mc5cti469ppvl6539qjj0mk",
        "u87wqe6lwzo6aorkvj_onfyl706a-pbj1gh",
        "unn2e7x4m7zilg57gr_3_x08w6ig89ihv7gf7j7fxbnap-p",
        "wgjj1c-_bxs9h16f_w366sojwe-9p5pks1ghzn6eol",
        "wnqksjf8sxj-o3_-9n7slqxhlz8e3u8do2tixi_t9_jjim72",
        "xkjn30fyl1cpp5ordg5cmjp9mtwdox767evp9rse6b2",
        "y93f2lwurfzvq-jj1ffnnr",
        "ye6-8ququogb0n722ucxf_der9",
        "z6l7enmqd-nxthgxl",
        "zl_l9gxwnkd3exeaq6g-48tce92zdaax2",
        "zq0sqe0088_9wmr70jkxaw",
        "long-key-été-ÉtÉ-mixed-case",
        "long-key-стоп-cyrillic-words",
        "long-key-回复-cjk-bytes-here",
        "àáâãäåæçèéêë-latin",
    ]
);

#[test]
fn single_key_on_either_side_of_the_long_key_split() {
    fn one_long(key: &[u8]) -> Option<u8> {
        hashify::map! { key, u8,
            "a" => 1, "bb" => 2, "ccc" => 3, "dddd" => 4, "eeeee" => 5, "ffffff" => 6,
            "ggggggg" => 7, "hhhhhhhh" => 8, "iiiiiiiii" => 9, "jjjjjjjjjj" => 10,
            "kkkkkkkkkkk" => 11, "llllllllllll" => 12, "mmmmmmmmmmmmm" => 13,
            "nnnnnnnnnnnnnn" => 14, "ooooooooooooooo" => 15, "pppppppppppppppp" => 16,
            "qq" => 17, "the only key longer than sixteen bytes" => 18,
        }
        .copied()
    }
    fn one_short(key: &[u8]) -> bool {
        hashify::set! { key,
            "short",
            "long key number 01", "long key number 02", "long key number 03",
            "long key number 04", "long key number 05", "long key number 06",
            "long key number 07", "long key number 08", "long key number 09",
            "long key number 10", "long key number 11", "long key number 12",
            "long key number 13", "long key number 14", "long key number 15",
            "long key number 16", "long key number 17",
        }
    }

    check(
        &pairs! {
            b"a" => 1, b"bb" => 2, b"ccc" => 3, b"dddd" => 4, b"eeeee" => 5, b"ffffff" => 6,
            b"ggggggg" => 7, b"hhhhhhhh" => 8, b"iiiiiiiii" => 9, b"jjjjjjjjjj" => 10,
            b"kkkkkkkkkkk" => 11, b"llllllllllll" => 12, b"mmmmmmmmmmmmm" => 13,
            b"nnnnnnnnnnnnnn" => 14, b"ooooooooooooooo" => 15, b"pppppppppppppppp" => 16,
            b"qq" => 17, b"the only key longer than sixteen bytes" => 18,
        },
        false,
        one_long,
    );
    let long_keys: Vec<String> = (1..=17)
        .map(|idx| format!("long key number {idx:02}"))
        .collect();
    let mut keys: Vec<(&[u8], bool)> = long_keys.iter().map(|key| (key.as_bytes(), true)).collect();
    keys.push((b"short", true));
    check(&keys, false, |key| one_short(key).then_some(true));
}
