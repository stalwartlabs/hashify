/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

#[path = "../benches/synthetic-keys/src/keys.rs"]
mod keys;

use std::env;
use std::fmt::{self, Display, Formatter};
use std::fs::{self, File};
use std::io::{self, Error};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant, SystemTime};

const DEFAULT_SIZES: [usize; 3] = [1_000, 10_000, 100_000];
const MATCH_MAX_KEYS: usize = 10_000;
const MAX_SAMPLES: usize = 10;
const SAMPLE_BUDGET: Duration = Duration::from_secs(30);
const EMPTY_SOURCE: &str = "pub fn lookup() {}\n";

#[derive(Clone, Copy, PartialEq, Eq)]
enum Implementation {
    Match,
    Phf,
    PhfPtrhash,
    Hashify,
}

#[derive(Clone, Copy)]
enum MacroProfile {
    Unoptimized,
    Optimized,
}

struct Source<'x> {
    implementation: Implementation,
    keys: &'x [String],
}

struct Project {
    dir: PathBuf,
    target_dir: PathBuf,
}

#[derive(Clone, Copy)]
struct Times {
    unoptimized: Duration,
    optimized: Option<Duration>,
}

impl Implementation {
    const ALL: [Implementation; 4] = [Self::Match, Self::Phf, Self::PhfPtrhash, Self::Hashify];

    fn name(self) -> &'static str {
        match self {
            Self::Match => "match",
            Self::Phf => "phf",
            Self::PhfPtrhash => "phf-ptrhash",
            Self::Hashify => "hashify",
        }
    }

    fn header(self) -> &'static str {
        match self {
            Self::Match => "`match`",
            Self::Phf => "phf",
            Self::PhfPtrhash => "phf `ptrhash`",
            Self::Hashify => "hashify `map!`",
        }
    }

    fn dependency(self) -> String {
        match self {
            Self::Match => String::new(),
            Self::Phf => r#"phf = { version = "0.14.0", features = ["macros"] }"#.to_owned(),
            Self::PhfPtrhash => {
                r#"phf = { version = "0.14.0", features = ["macros", "ptrhash"] }"#.to_owned()
            }
            Self::Hashify => format!("hashify = {{ path = {:?} }}", env!("CARGO_MANIFEST_DIR")),
        }
    }

    fn baseline(self) -> Option<Implementation> {
        (self == Self::Hashify).then_some(Self::Phf)
    }

    fn measure(self, root: &Path, keys: &[String]) -> io::Result<Option<Times>> {
        if self == Self::Match && keys.len() > MATCH_MAX_KEYS {
            return Ok(None);
        }
        let source = Source {
            implementation: self,
            keys,
        }
        .to_string();
        let unoptimized =
            Project::new(root, self, MacroProfile::Unoptimized)?.build_time(&source)?;
        let optimized = if self == Self::Match {
            None
        } else {
            Some(Project::new(root, self, MacroProfile::Optimized)?.build_time(&source)?)
        };
        Ok(Some(Times {
            unoptimized,
            optimized,
        }))
    }
}

impl Times {
    fn describe(&self, baseline: Option<&Times>) -> String {
        let unoptimized = seconds_with_speedup(
            self.unoptimized,
            baseline.map(|baseline| baseline.unoptimized),
        );
        match self.optimized {
            Some(optimized) => format!(
                "{unoptimized} / {}",
                seconds_with_speedup(optimized, baseline.and_then(|baseline| baseline.optimized))
            ),
            None => unoptimized,
        }
    }
}

impl MacroProfile {
    fn name(self) -> &'static str {
        match self {
            Self::Unoptimized => "unoptimized",
            Self::Optimized => "optimized",
        }
    }

    fn manifest_section(self) -> &'static str {
        match self {
            Self::Unoptimized => "",
            Self::Optimized => "[profile.release.build-override]\nopt-level = 3\n",
        }
    }
}

impl Display for Source<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let entries = self.keys.iter().enumerate();
        match self.implementation {
            Implementation::Match => {
                writeln!(f, "pub fn lookup(key: &str) -> Option<u32> {{")?;
                writeln!(f, "    match key {{")?;
                for (idx, key) in entries {
                    writeln!(f, "        {key:?} => Some({idx}),")?;
                }
                writeln!(f, "        _ => None,")?;
                writeln!(f, "    }}")?;
                writeln!(f, "}}")
            }
            Implementation::Phf | Implementation::PhfPtrhash => {
                writeln!(
                    f,
                    "pub static MAP: phf::Map<&'static str, u32> = phf::phf_map! {{"
                )?;
                for (idx, key) in entries {
                    writeln!(f, "    {key:?} => {idx},")?;
                }
                writeln!(f, "}};")
            }
            Implementation::Hashify => {
                writeln!(f, "pub fn lookup(key: &[u8]) -> Option<&'static u32> {{")?;
                writeln!(f, "    hashify::map! {{ key, u32,")?;
                for (idx, key) in entries {
                    writeln!(f, "        {key:?} => {idx},")?;
                }
                writeln!(f, "    }}")?;
                writeln!(f, "}}")
            }
        }
    }
}

impl Project {
    fn new(root: &Path, implementation: Implementation, profile: MacroProfile) -> io::Result<Self> {
        let name = format!("{}-{}", implementation.name(), profile.name());
        let dir = root.join(&name);
        fs::create_dir_all(dir.join("src"))?;
        let manifest = format!(
            "[package]\nname = \"build-time-{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
             publish = false\n\n[dependencies]\n{}\n\n{}\n[workspace]\n",
            implementation.dependency(),
            profile.manifest_section(),
        );
        let manifest_path = dir.join("Cargo.toml");
        if fs::read_to_string(&manifest_path).ok().as_deref() != Some(manifest.as_str()) {
            fs::write(&manifest_path, manifest)?;
        }
        Ok(Project {
            dir,
            target_dir: root.join("target"),
        })
    }

    fn source_path(&self) -> PathBuf {
        self.dir.join("src").join("lib.rs")
    }

    fn build_time(&self, source: &str) -> io::Result<Duration> {
        fs::write(self.source_path(), EMPTY_SOURCE)?;
        self.build()?;
        let baseline = self.fastest_rebuild(Vec::new())?;
        fs::write(self.source_path(), source)?;
        let first = self.build()?;
        let with_lookup = self.fastest_rebuild(vec![first])?;
        Ok(with_lookup.saturating_sub(baseline))
    }

    fn fastest_rebuild(&self, mut samples: Vec<Duration>) -> io::Result<Duration> {
        while samples.len() < MAX_SAMPLES && samples.iter().sum::<Duration>() < SAMPLE_BUDGET {
            File::options()
                .write(true)
                .open(self.source_path())?
                .set_modified(SystemTime::now())?;
            samples.push(self.build()?);
        }
        Ok(samples.into_iter().min().unwrap_or_default())
    }

    fn build(&self) -> io::Result<Duration> {
        let start = Instant::now();
        let status = Command::new(env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
            .args(["build", "--release", "--quiet"])
            .current_dir(&self.dir)
            .env("CARGO_TARGET_DIR", &self.target_dir)
            .status()?;
        let elapsed = start.elapsed();
        if status.success() {
            Ok(elapsed)
        } else {
            Err(Error::other(format!(
                "cargo build failed in {}",
                self.dir.display()
            )))
        }
    }
}

fn seconds(duration: Duration) -> String {
    format!("{:.2} s", duration.as_secs_f64())
}

fn seconds_with_speedup(duration: Duration, baseline: Option<Duration>) -> String {
    match baseline {
        Some(baseline) => format!(
            "{} (**{:.1}x**)",
            seconds(duration),
            baseline.as_secs_f64() / duration.as_secs_f64()
        ),
        None => seconds(duration),
    }
}

fn thousands(value: usize) -> String {
    let digits = value.to_string();
    let mut grouped = String::with_capacity(digits.len() + digits.len() / 3);
    for (idx, digit) in digits.chars().enumerate() {
        if idx > 0 && (digits.len() - idx).is_multiple_of(3) {
            grouped.push(',');
        }
        grouped.push(digit);
    }
    grouped
}

fn main() -> io::Result<()> {
    let sizes = env::args()
        .skip(1)
        .map(|arg| arg.replace('_', "").parse().map_err(Error::other))
        .collect::<io::Result<Vec<usize>>>()?;
    let sizes = if sizes.is_empty() {
        DEFAULT_SIZES.to_vec()
    } else {
        sizes
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("build-time");

    let mut rows = Vec::with_capacity(sizes.len());
    for size in sizes {
        let keys = keys::generate(size);
        let measured = Implementation::ALL
            .into_iter()
            .map(|implementation| {
                let times = implementation.measure(&root, &keys)?;
                eprintln!(
                    "{} keys, {}: {}",
                    thousands(size),
                    implementation.name(),
                    times.map_or_else(|| "n/a".to_owned(), |times| times.describe(None))
                );
                Ok((implementation, times))
            })
            .collect::<io::Result<Vec<_>>>()?;
        let cells: Vec<String> = measured
            .iter()
            .map(|&(implementation, times)| {
                let baseline = implementation.baseline().and_then(|baseline| {
                    measured
                        .iter()
                        .find(|&&(other, _)| other == baseline)
                        .and_then(|(_, times)| times.as_ref())
                });
                times.map_or_else(|| "n/a".to_owned(), |times| times.describe(baseline))
            })
            .collect();
        rows.push(format!("| {} | {} |", thousands(size), cells.join(" | ")));
    }

    println!(
        "| Keys | {} |",
        Implementation::ALL.map(Implementation::header).join(" | ")
    );
    println!("|---|{}", "---|".repeat(Implementation::ALL.len()));
    for row in rows {
        println!("{row}");
    }
    Ok(())
}
