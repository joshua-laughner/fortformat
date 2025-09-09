# Fortformat Changelog

## v0.2.0

Added a serialization option to permit skipping struct fields or map keys
not listed in the field order slice.

Previously, if you had a struct with fields `alpha` and `beta`, calling a
function such as `to_string_with_fields` with only `["beta"]` as the `fields`
argument would produce an error. Now, you can use the `to_*_custom` functions
with a `SerSettings` instance with `allow_skipped_fields` set to `true` to
only serialize fields that are included in that list.

## v0.1.2

Fixed a bug when serializing a value of 0 with an "e" or "d" format specifier.

## v0.1.1

Added docs.rs metadata to ensure that the documentation for all features is built.

## v0.1.0

Initial release, with the following features:

- Parse Fortran fixed format strings containing character, integer (decimal, octal, or hexadecimal), real, logical, and skip fields
  along with precision scaling modifiers.
- Recognize and handle list-directed Fortran I/O (i.e., the `*` format)
- Serialize or deserialize most serde-compatible types following a Fortran format string
- Limited support for deserializing directly to Polars dataframes.
