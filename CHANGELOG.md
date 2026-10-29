# Change Log

All notable changes to this project will be documented in this file. This project adheres to [Semantic Versioning](https://semver.org/).

## [0.3.2] - Unreleased

### Fixed
- Tests compile on 32-bit targets (#7).
- Maps and sets of 4 to 16 keys use the flat table instead of a `match` tree, whose jump table mispredicted on random input (#6).
