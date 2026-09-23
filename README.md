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

Median time per lookup, measured with [criterion](https://crates.io/crates/criterion) on an Apple M5 Max with Rust 1.98. `hits` looks up every key once, in the order the keys are listed. `random` performs 4096 lookups in a pseudo-random order, half of them for keys that differ from a member by one bit. The synthetic keys are random strings of 3 to 21 bytes over `[a-z0-9_-]`, 12 bytes long on average, and 15% of them are longer than 16 bytes.

`match` is a plain `match` on the key with one string arm per key. phf is [phf](https://crates.io/crates/phf) 0.14 with its default CHD layout, and phf `ptrhash` is the same crate built with its experimental `ptrhash` feature, which replaces CHD with a PtrHash-style table of 8-bit pilots. Both layouts hash every key with SipHash-1-3. The figure in bold is how many times faster hashify is than phf with its default layout.

| Keys | Workload | `match` | phf | phf `ptrhash` | hashify `map!` | hashify `fnc_map!` |
|---|---|---|---|---|---|---|
| HTTP methods (9) | hits | 1.34 ns | 8.62 ns | 6.01 ns | 0.68 ns (**12.6x**) | 0.68 ns (**12.7x**) |
| HTTP methods (9) | random | 1.91 ns | 8.37 ns | 5.80 ns | 1.53 ns (**5.5x**) | 1.53 ns (**5.5x**) |
| IMAP commands (26) | hits | 1.73 ns | 9.35 ns | 6.01 ns | 0.89 ns (**10.5x**) | 0.87 ns (**10.8x**) |
| IMAP commands (26) | random | 2.51 ns | 8.77 ns | 6.07 ns | 1.37 ns (**6.4x**) | 1.02 ns (**8.6x**) |
| Sieve keywords (128) | hits | 2.75 ns | 8.85 ns | 6.41 ns | 1.77 ns (**5.0x**) | 1.93 ns (**4.6x**) |
| Sieve keywords (128) | random | 7.54 ns | 8.69 ns | 6.09 ns | 1.82 ns (**4.8x**) | 1.94 ns (**4.5x**) |
| Charset names (149) | hits | 2.74 ns | 9.73 ns | 6.86 ns | 1.93 ns (**5.0x**) | 1.85 ns (**5.3x**) |
| Charset names (149) | random | 7.80 ns | 9.31 ns | 6.47 ns | 1.97 ns (**4.7x**) | 1.93 ns (**4.8x**) |
| HTML entities (2125) | hits | 25.1 ns | 9.08 ns | 6.34 ns | 1.85 ns (**4.9x**) | 1.95 ns (**4.7x**) |
| HTML entities (2125) | random | 39.8 ns | 8.71 ns | 5.96 ns | 1.84 ns (**4.7x**) | 1.93 ns (**4.5x**) |
| Synthetic keys (10,000) | hits | n/a | 10.2 ns | 7.55 ns | 1.60 ns (**6.4x**) | n/a |
| Synthetic keys (10,000) | random | n/a | 9.89 ns | 7.18 ns | 1.59 ns (**6.2x**) | n/a |
| Synthetic keys (100,000) | hits | n/a | 13.6 ns | 12.4 ns | 3.33 ns (**4.1x**) | n/a |
| Synthetic keys (100,000) | random | n/a | 10.8 ns | 7.59 ns | 2.22 ns (**4.8x**) | n/a |

hashify's `map!` is **3.2** to **8.8 times** faster than phf with `ptrhash` and **4.1x** to **12.6x faster** than phf with the default layout. A `match` stays within a factor of two of hashify on the HTTP methods and IMAP commands, falls four times behind on the Sieve keywords and charset names in random order, and needs 25 to 40 ns per lookup among the 2125 HTML entities. `match` and `fnc_map!` are not measured on the synthetic key sets because of their build times.

### Build time

hashify builds its tables while the macro expands, so a large key set costs build time. The table lists how many seconds one lookup adds to a release build of a crate that contains nothing else. Each cell gives the time with Cargo's defaults, which compile proc macros without optimizations, followed by the time with the `opt-level = 3` setting enabled. The figures in bold are how many times faster hashify builds than phf with its default layout.

| Keys | `match` | phf | phf `ptrhash` | hashify `map!` |
|---|---|---|---|---|
| 1,000 | 0.58 s | 0.02 s / 0.02 s | 0.02 s / 0.02 s | 0.04 s (**0.6x**) / 0.04 s (**0.5x**) |
| 10,000 | 58.08 s | 0.24 s / 0.18 s | 0.21 s / 0.17 s | 0.19 s (**1.2x**) / 0.14 s (**1.3x**) |
| 100,000 | n/a | 2.98 s / 2.22 s | 2.61 s / 2.04 s | 2.59 s (**1.1x**) / 1.67 s (**1.3x**) |
| 1,000,000 | n/a | 41.77 s / 29.16 s | 32.92 s / 26.82 s | 24.07 s (**1.7x**) / 15.24 s (**1.9x**) |

A `match` with 10,000 string arms takes 58 s to compile, so larger ones are not measured. `fnc_map!` builds the same tables as `map!` but compiles every arm into one function, and in a release build LLVM spends about 4 s optimizing one with 10,000 arms.

rustc runs a proc macro again every time it compiles the crate that invokes it, incremental builds included, so a large lookup is best kept in a crate of its own. hashify builds its tables at compile time only and cannot rebuild them at runtime.

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
$ cargo bench --bench lookup
$ cargo bench --bench lookup --features phf/ptrhash -- phf_ptrhash
$ cargo run --release --example build_time
```

The second benchmark command rebuilds phf with its `ptrhash` feature and runs only the phf benchmarks. Cargo enables a crate's features for the whole build, so one binary cannot measure both phf layouts. The synthetic key sets are compiled only when debug assertions are off, which keeps them out of `cargo check`, `cargo test` and rust-analyzer. `build_time` accepts key counts as arguments, as in `cargo run --release --example build_time -- 1000000`.

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Copyright

Copyright (C) 2025, Stalwart Labs LLC
