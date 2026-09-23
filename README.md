# hashify

[![crates.io](https://img.shields.io/crates/v/hashify)](https://crates.io/crates/hashify)
[![docs.rs](https://img.shields.io/docsrs/hashify)](https://docs.rs/hashify)
[![crates.io](https://img.shields.io/crates/l/hashify)](http://www.apache.org/licenses/LICENSE-2.0)

_hashify_ is a procedural macro crate that builds perfect hash lookups for maps, sets and match-style dispatch at compile time. The generated code has no runtime dependencies, never allocates and contains no `unsafe` code.

Each invocation picks its own lookup strategy from the number of keys: a `gperf --switch` style decision tree for small sets, a single-hash table for medium sets, and a minimal perfect hash function with 8-bit pilots, derived from [PtrHash](https://arxiv.org/abs/2502.15539) and [PHast](https://arxiv.org/abs/2504.17918), for large ones.

## Macros

| Macro | Returns |
|---|---|
| `map!(key, Type, "k" => value, ...)` | `Option<&'static Type>` |
| `set!(key, "k", ...)` | `bool` |
| `fnc_map!(key, "k" => expr, ..., _ => default)` | the value of the matching arm, or of `default` |
| `map_ignore_case!`, `set_ignore_case!`, `fnc_map_ignore_case!` | the same, ignoring ASCII case |

`key` is an expression that can be sliced to `&[u8]`: a byte slice, a byte array or a reference to one, or a `Vec<u8>`. Pass strings with `as_bytes()`.

Keys are literals: strings, byte strings, byte arrays, characters, booleans and integers. Integer keys are matched against their big-endian bytes, so `1u16` matches `[0, 1]`.

`map!` stores its values in a `static` table, so they must be constant expressions. `fnc_map!` evaluates an arm only when its key matches, so arms can be any expression, including blocks with side effects, `return` or `?`.

The `_ignore_case` variants fold `A`-`Z` only. Bytes outside ASCII must match exactly.

## Usage

Maps:

```rust
fn charset(name: &str) -> Option<u32> {
    hashify::map! {
        name.as_bytes(),
        u32,
        "koi8_r" => 35,
        "windows_1253" => 97,
        "windows_1257" => 114,
        "iso_8859_10" => 69,
        "windows_1251" => 70,
        "ks_c_5601_1989" => 64,
    }
    .copied()
}

assert_eq!(charset("koi8_r"), Some(35));
assert_eq!(charset("utf8"), None);
```

Sets:

```rust
fn is_reply_prefix(prefix: &str) -> bool {
    hashify::set_ignore_case! {
        prefix.as_bytes(),
        "re", "res", "sv", "antw", "ref", "aw", "απ", "השב", "vá", "r", "rif", "bls", "odp",
        "ynt", "atb", "رد", "回复", "转发",
    }
}

assert!(is_reply_prefix("RE"));
assert!(is_reply_prefix("回复"));
```

Function maps:

```rust
fn command(input: &str) -> Result<(), String> {
    hashify::fnc_map_ignore_case!(input.as_bytes(),
        "ALL" => {
            println!("All");
        },
        "FULL" => {
            println!("Full");
        },
        "ENVELOPE" => {
            println!("Envelope");
        },
        _ => {
            return Err(format!("Unknown command {input}"));
        }
    );
    Ok(())
}
```

## Performance

Median time for one pass over each workload, measured with [criterion](https://crates.io/crates/criterion) against [phf](https://crates.io/crates/phf) 0.14 on an Apple M5 Max with Rust 1.98. `hits` looks up every key once, always in the same order. `random` performs 4096 lookups in a pseudo-random order, half of them for keys that differ from a member by one bit.

| Keys | Workload | phf | hashify `map!` | hashify `fnc_map!` |
|---|---|---|---|---|
| HTTP methods (9) | hits | 8.38 ns | 0.67 ns (12.4x) | 0.68 ns (12.4x) |
| HTTP methods (9) | random | 8.23 ns | 1.51 ns (5.4x) | 1.50 ns (5.5x) |
| IMAP commands (26) | hits | 8.69 ns | 0.93 ns (9.4x) | 0.88 ns (9.8x) |
| IMAP commands (26) | random | 8.55 ns | 1.00 ns (8.6x) | 1.12 ns (7.6x) |
| Sieve keywords (128) | hits | 8.72 ns | 1.73 ns (5.0x) | 1.96 ns (4.5x) |
| Sieve keywords (128) | random | 8.41 ns | 1.80 ns (4.7x) | 1.89 ns (4.5x) |
| Charset names (149) | hits | 9.54 ns | 1.68 ns (5.7x) | 1.72 ns (5.5x) |
| Charset names (149) | random | 9.22 ns | 1.76 ns (5.2x) | 2.14 ns (4.3x) |
| HTML entities (2125) | hits | 8.93 ns | 1.72 ns (5.2x) | 1.76 ns (5.1x) |
| HTML entities (2125) | random | 8.66 ns | 1.82 ns (4.8x) | 1.90 ns (4.5x) |

Run the benchmarks with `cargo bench`.

## Lookup strategies

The macro splits the keys by length. Keys of up to 16 bytes are stored in a table as two 64-bit words read from both ends of the key plus the key length, so a lookup compares three integers and never calls `memcmp` or follows a pointer. Longer keys go to a second table and are compared eight bytes at a time.

Each table uses one of three strategies:

- **Up to 16 keys**: a decision tree of `match` statements on the key length and on one byte, or the XOR of two bytes, that tells the keys apart. This is the approach of `gperf --switch`, and the compiler turns it into jump tables and inline comparisons against constants.
- **17 to 64 keys**: a flat table. The macro searches for a seed that sends every key to its own slot in a power-of-two table, so a lookup is one multiplication, a shift and one table load.
- **More than 64 keys**: a minimal perfect hash function. Keys are grouped into buckets, each bucket stores one byte (its pilot), and a key's slot is computed from its hash and the pilot with two multiply-high operations. The pilot search evicts conflicting buckets the way cuckoo hashing does, which is what lets one byte per bucket suffice. For typical inputs the table ends up with exactly one slot per key. Larger or harder key sets fall back to at most 5% spare slots.

The macro builds a second set of tables from a 32-bit hash and selects it with `#[cfg(target_pointer_width)]`, so 32-bit targets do not pay for 64-bit multiplication.

## Testing and benchmarking

```bash
$ cargo test
$ cargo bench
```

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Copyright

Copyright (C) 2025, Stalwart Labs LLC
