# hashify

[![crates.io](https://img.shields.io/crates/v/hashify)](https://crates.io/crates/hashify)
[![docs.rs](https://img.shields.io/docsrs/hashify)](https://docs.rs/hashify)
[![crates.io](https://img.shields.io/crates/l/hashify)](http://www.apache.org/licenses/LICENSE-2.0)

_hashify_ is a Rust procedural macro crate designed to create perfect hashing maps and sets without any runtime dependencies. By combining traditional and modern hashing techniques, _hashify_ ensures exceptional speed and efficiency, making it a great tool for developers seeking optimal performance in their projects.

It provides two distinct approaches for building maps and sets, tailored for different dataset sizes:
- For **small maps** with fewer than 500 entries, _hashify_ uses a strategy similar to [GNU gperf](https://www.gnu.org/software/gperf/) with the `--switch` parameter. This approach is highly efficient and specifically optimized for small datasets. 
- For **larger datasets**, _hashify_ employs the [PTHash](https://arxiv.org/abs/2104.10402) algorithm. This Minimal Perfect Hashing algorithm ensures both compactness and speed, making it ideal for scaling to larger datasets without compromising performance.

## Performance

_hashify_ was designed with performance as a top priority, and its benchmarks demonstrate this:
- For tiny maps, _hashify_ is over **4 times faster** than the Rust [phf](https://crates.io/crates/phf) crate (which uses the [CHD algorithm](http://cmph.sourceforge.net/papers/esa09.pdf) algorithm).
- For large maps, _hashify_ achieves a consistent **40% speed** improvement compared to `phf`. These results highlight its suitability for developers who require exceptional speed and efficiency in their hash map and set operations.

## Features

- **Perfect Hashing**: Generates collision-free lookup tables for your **maps**, **sets** and **functions** at compile time.
- **No Runtime Dependencies**: Everything is computed at compile time, making it ideal for environments where performance and binary size matter.
- **Multiple hashing strategies**: _Tiny maps_ for datasets smaller than 500 entries and _large maps_ using the PTHash Minimal Perfect Hashing algorithm.
- **Fast**: Tiny maps are over **4x faster** than the CHD algorithm, while large maps are approximately **40% faster**.

## Limitations

_hashify_, since it uses the [Fowler–Noll–Vo 1a](https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function#FNV-1a_hash) hashing algorithm, is designed to work best with maps consisting of short byte slices (1 to 50 bytes). This makes it highly efficient for such datasets, but it may not perform as well with longer or more complex keys. However, modifying the crate to use other hashing algorithms is trivial, and we invite those interested in alternative algorithms to open a GitHub issue to discuss and potentially add support for other hashing options.

## Usage Example

Maps:

```rust
fn tiny_map_get(key: &str) -> Option<u32> {
    hashify::tiny_map! {
        key.as_bytes(),
        "koi8_r" => 35,
        "windows_1253" => 97,
        "windows_1257" => 114,
        "iso_8859_10" => 69,
        "windows_1251" => 70,
        "ks_c_5601_1989" => 64,
    }
}

fn large_map_get(key: &str) -> Option<&u32> {
    hashify::map! {
        key.as_bytes(),
        u32,
        "koi8_r" => 35,
        "windows_1253" => 97,
        "windows_1257" => 114,
        "iso_8859_10" => 69,
        "windows_1251" => 70,
        "ks_c_5601_1989" => 64,
    }
}

fn main() {
    assert_eq!(tiny_map_get("koi8_r"), Some(35));
    assert_eq!(large_map_get("koi8_r"), Some(35));
}
```

Sets:

```rust
fn tiny_set_contains(prefix: &str) -> bool {
    hashify::tiny_set! { prefix.as_bytes(),"re", "res", "sv", "antw", "ref", "aw", "απ", "השב", "vá", "r", "rif", "bls", "odp", "ynt", "atb", "رد", "回复", "转发", }
}

fn large_set_contains(prefix: &str) -> bool {
    hashify::set! { prefix.as_bytes(), "fwd", "fw", "rv","enc", "vs", "doorst", "vl", "tr", "wg", "πρθ", "הועבר", "továbbítás", "i", "fs", "trs", "vb", "pd", "i̇lt", "yml", "إعادة توجيه", "回覆", "轉寄", }
}

fn main() {
    assert!(tiny_set_contains("回复"));
    assert!(large_set_contains("továbbítás"));
}
```

Function maps:

```rust
fn main() {
    hashify::fnc_map_ignore_case!(input.as_bytes(),
        "ALL" => {
            println!("All");
        },
        "FULL" => {
            println!("Full");
        },
        "FAST" => {
            println!("Fast");
        },
        "ENVELOPE" => {
            println!("Envelope");
        },
        _ => {
            eprintln!("Unknown command {input}");
        }
    );
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
