# hashify

[![crates.io](https://img.shields.io/crates/v/hashify)](https://crates.io/crates/hashify)
[![build](https://github.com/stalwartlabs/hashify/actions/workflows/rust.yml/badge.svg)](https://github.com/stalwartlabs/hashify/actions/workflows/rust.yml)
[![docs.rs](https://img.shields.io/docsrs/hashify)](https://docs.rs/hashify)
[![crates.io](https://img.shields.io/crates/l/hashify)](http://www.apache.org/licenses/LICENSE-2.0)

_hashify_ is a Rust procedural macro that generates **perfect hash lookup tables** at compile time. It provides a highly optimized solution for creating small, static maps without any runtime dependencies. Inspired by the design principles of [GNU gperf](https://www.gnu.org/software/gperf/), _hashify_ offers unparalleled performance for its target use cases, being more than **4 times faster** than the widely-used [phf](https://crates.io/crates/phf) crate (which relies on the [CHD algorithm](http://cmph.sourceforge.net/papers/esa09.pdf)).

_hashify_ is best suited for **small maps** with fewer than **500 entries**. It is perfect for applications such as writing parsers, building lightweight command-line utilities or creating mappings for static configuration values. For **larger datasets** (greater than 500 entries), crates like `phf` or similar options may be more appropriate as their algorithms scales better for large lookup tables.

## Features

- **Perfect Hashing**: Generates collision-free lookup tables for your data at compile time.
- **No Runtime Dependencies**: Everything is computed at compile time, making it ideal for environments where performance and binary size matter.
- **Fast**: Benchmarks show that _hashify_ is **4x faster** than `phf` for small datasets. This makes it the go-to choice for scenarios where high performance with small datasets is critical.
- **Ideal for Parsers**: Perfect for building parsers or other applications that involve small, static mappings.

## Usage Example

```rust
fn lookup_charsets(key: &[u8]) -> Option<u32> {
    hashify::map! {
        key,
        "koi8_r" => 35,
        "windows_1253" => 97,
        "windows_1257" => 114,
        "iso_8859_10" => 69,
        "windows_1251" => 70,
        "ks_c_5601_1989" => 64,
    }
}

fn main() {
    assert_eq!(lookup_charsets("koi8_r"), Some(35));
}
```

## Testing, Fuzzing & Benchmarking

To run the testsuite:

```bash
 $ cargo test --all-features
```

and, to run the benchmarks:

```bash
 $ cargo bench --all-features
```

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Copyright

Copyright (C) 2025, Stalwart Labs LLC
