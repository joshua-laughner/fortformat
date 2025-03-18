# FortFormat

![Crates.io Version](https://img.shields.io/crates/v/fortformat)

A Rust parser for Fortran format strings.

Copyright 2024, by the California Institute of Technology.
ALL RIGHTS RESERVED.
United States Government Sponsorship acknowledged.
Any commercial use must be negotiated with the Office of Technology Transfer at the California Institute of Technology.
 
This software may be subject to U.S. export control laws.
By accepting this software, the user agrees to comply with all applicable U.S. export laws and regulations.
User has the responsibility to obtain export licenses, or other export authority as may be required before exporting such information to foreign countries or providing access to foreign persons.

## Overview

The Fortran language is heavily used in STEM fields, and has the built-in ability to read and write data following fixed-width formats.
Specifying these formats is a mini-language within Fortran, which makes interpreting fixed-width data challenging, especially since it does not need to have its values separated by whitespace.
The purpose of this crate is to handle parsing these Fortran format specification strings as well as serializing data to or deserializing data from those formats using [`serde`](https://serde.rs/).

## Usage

Minimum supported Rust version is currently 1.63.0.

Add this as a dependency to your project with `cargo add fortformat` or directly adding the following to your `Cargo.toml`:

```toml
fortformat = "0.1.0"
```

By default, only parsing the format strings is active.
To enable serialization and deserialization, include the `serde` feature with `cargo add fortformat --features=serde` or

```toml
fortformat = {version = "0.1.0", features = ["serde"]}
```

To include deserialization into Polars dataframes, also add the `dataframes` feature with `cargo add fortformat --features=serde,dataframes` or

```toml
fortformat = {version = "0.1.0", features = ["serde", "dataframes"]}
```

To parse format strings, import the `FortFormat` type into your project and call its `parse` method on the format string:

```rust
use fortformat::FortFormat;
let fmt_str = "(a,i3)";
let fmt = FortFormat::parse(fmt_str).unwrap();
```

To deserialize data written following a Fortran format string, first parse the string as above, then use any of the various `from_*` methods available in the crate root and in the `de` module.
Similarly, to serialize, parse the format string (or otherwise construct the desired format) and use any of the `to_*` methods available in the crate root and in the `ser` module.


## Implemented features

There are many details to fully parsing Fortran format string and serializing/deserializing data following such strings.
We have focused on first implementing features needed for our own work.
The following features have been implemented to date:

- Parse Fortran fixed format strings containing character, integer (decimal, octal, or hexadecimal), real, logical, and skip fields
  along with precision scaling modifiers.
- Recognize and handle list-directed Fortran I/O (i.e., the `*` format)
- Serialize or deserialize most serde-compatible types following a Fortran format string
- Limited support for deserializing directly to Polars dataframes.

## Missing features

There remain some aspects of handling Fortran format strings and formatted data to implement.
This includes:

- `T`, `TL`, and `TR` positional specifiers
- `R` specifier for "remainder of input"
- Complex numbers
- Radix editing specifiers
- Slash specifier for end of record
- Colon specifider for early termination of record
- Serialization to and deserialization from "g" format for real numbers
- Deserialization of enums

If you find a feature of Fortran format strings missing that you need for your project, please [open an issue](https://github.com/joshua-laughner/fortformat/issues) with a minimum working example of the data and associated format.
Having real examples helps us build test cases to ensure that this crate follows Fortran formatting as closely as possible, given the differences between Fortran and Rust.
