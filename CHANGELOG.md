# Fortformat Changelog

## v0.1.1

Added docs.rs metadata to ensure that the documentation for all features is built.

## v0.1.0

Initial release, with the following features:

- Parse Fortran fixed format strings containing character, integer (decimal, octal, or hexadecimal), real, logical, and skip fields
  along with precision scaling modifiers.
- Recognize and handle list-directed Fortran I/O (i.e., the `*` format)
- Serialize or deserialize most serde-compatible types following a Fortran format string
- Limited support for deserializing directly to Polars dataframes.
