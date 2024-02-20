//! Parse and work with Fortran format specifications.
//! 
//! # Crate structure
//! 
//! Most users should focus on the following four modules:
//! 
//! - [`format_specs`]: handles parsing the format strings and provides
//!   types to represent each one in Rust. If you just need to get information
//!   about a format string, try this module.
//! - [`ser`], [`de`]: handles serializing and deserializing data in Fortran
//!   fixed format using the [`serde`] crate. Requires the `serde` feature
//!   be activated.
//! - [`dataframes`]: an extension of the `serde` functionality which allows
//!   deserializing multiple rows of data into a [`polars`] DataFrame. Requires
//!   the `dataframes` feature be activated.
//! 
//! Many of the public functions are also available in the crate root.
//! 
//! # What are format specifications?
//! 
//! Fortran programs can write and read data using fixed format.
//! In fixed format, each piece of data is written to a text or binary
//! file with a specific number of bytes. When reading or writing
//! text, the formatting for each value is given by a format string,
//! which will look something like:
//! 
//! ```text
//! (a12,i5,f12.4,e11.5)
//! ```
//! 
//! The above string can be interpreted as:
//! 
//! - a string with 12 characters (`a12`),
//! - an integer that has 5 characters, including a negative sign if needed (`i5`),
//! - a float with  12 characters (including a decimal point and possibly a negative
//!   sign), and 4 digits after the decimal point, and
//! - a float written in engineering/scientific notation (e.g. `6.022E+23`) using 11
//!   characters and with 5 digits after the decimal place.
//! 
//! What makes such data tricky to read in more modern programming languages is
//! that these fields can and do abut. The following is a perfectly valid string
//! with the above format:
//! 
//! ```text
//! Hello,world!123459999999.99996.02214E+23
//! ```
//! 
//! The four values are actually `Hello,world!`, `12345`, `9999999.9999`, and `6.02214E+23`,
//! but without knowing the format string, it can be difficult to separate out the
//! values with no delimiting characters.
//! 
//! # A brief overview of format specs
//! 
//! Being such an old language, it can be difficult to find information about the Fortran format
//! syntax. Here is a short summary of the syntax as implemented in this crate (and tested against
//! gfortran-generated output).
//! 
//! ## Basic syntax
//! A format string starts with a `(`, followed by one or more fields separated by
//! commas, and ends with a `)`. (Alternate formats accepted by Fortran are not yet implemented.)
//! 
//! A field consists of a least a letter indicating the type to be written and how it is to be formatted.
//! It may be preceded by a number indicating how many times to repeat it, and followed by one or more
//! numbers (usually with a decimal point separator) that indicates its width and precision. A field
//! may also start with a modifier, which impacts all following fields until another modifier of the
//! same type is given.
//! 
//! ## Field types
//! 
//! - `a` = string/character type. `a` by itself means a single character. Strings are indicated
//!   by `aN`, e.g. `a5`, `a12`, or `a128`. The number gives the maximum number of characters in
//!   the string.
//! - `i` = integer type. Must have a width, that is, `i5` is valid but `i` alone is not. If a second
//!   number is given, as in `i5.3`, the second number indicates how wide the integer must be. If the
//!   integer has fewer digits than this, it is zero-padded. For example, `42` formatted as `i5.3` would
//!   be written as "  042" - 5 total width, 3 digits required. Fortran does not distinguish between
//!   signed and unsigned integers. A negative sign takes up one of the available characters given by the
//!   width.
//! - `f`, `e`, `d`, and `g` = real/float type. Must have both a width and precision, i.e. `f8.3` is
//!   valid, but neither `f8` nor `f` are. In these types, the number after the decimal (3 in `f8.3`)
//!   indicates the number of digits written after the decimal place. `f` will always write out numbers
//!   normally while `e` will use scientific/engineering notation (e.g. `6.022E+23`). `d` is similar to
//!   `e`, but is intended for 64-bit floats, and represents this with a `D` in place of the `E`: `6.022D+23`.
//!   `g` will choose the format based on the magnitude of the value.
//! - `x` = a *positional* specifier. This does not correspond to a value, it merely "positions" the next
//!    value. `x` represents a single space, and is the most common positional specifier.
//! 
//! ## Repeats and subgroups
//! 
//! A given specifier may be repeated by prefixing it with a number. For example, the string `(4i5.3)`
//! indicates that four, 5-character wide integers will be written. 
//! 
//! Multiple specifiers may be repeated by grouping them with parentheses. For example, the string
//! `(a12,3(i5,e13.5))` means one 12-character string will be written, followed by 3 sets consisting of
//! a 5-character integer and a 13-character float. Fully expanded, this will be:
//! 
//! ```text
//! (a12,i5,e13.5,i5,e13.5,i5,e13.5)
//! ```
//! 
//! ## Modifiers
//! 
//! - `p` = scale a real/float number before writing it. This is always written as `Np`, where `N` is
//!   a positive or negative integer. This has slightly different effects for `f` versus `e`/`d` formats. 
//!     - An `f` format means that the number will be multiplied by 10^N, so given a format `2pf7.3`, the
//!       number `3.14` would be written as `314.000`. Conversely, `-2pf7.3` would write it out as `  0.031`.
//!       In both cases, the number of digits after the decimal is unchanged at 3.
//!     - For `e` or `d` formats, the decimal place shifts when N > 1, so `2pe9.3` would print 3.14 as `31.40E-01`.
//!       For N < 0, it only shifts the place of the numbers, so `-2pe8.3` would print 3.14 as `0.003E+03`.
//!       N = 1 is a bit of a special case, in that it shifts the digits to write the value as e.g. `3.140E+00` instead
//!       of the default `0.314E+01`.
//!     - Note that `f` types actually have their value changed, while `e` and `d` types print the same value, just
//!       with different exponents.
//! 
//! Modifiers don't just affect the field they are attached to, but affect all releveant fields later in the format
//! string (until the next instance of the same modifier). So in a string like:
//! 
//! ```text
//! (f5.3,1pe12.5,e12.5,f6.3,-2pf7.5,f7.5)
//! ```
//! 
//! - the first `f5.3` is unaffected,
//! - the next `e12.5,e12.5,f6.3` are all affected by the `1p` modifier, and
//! - the final `f7.5,f7.5` are both affected by the `-2p` modifier.
extern crate pest;
#[macro_use]
extern crate pest_derive;
pub mod fort_error;
pub mod format_specs;
pub(crate) mod parsing;
#[cfg(feature = "serde")]
pub mod serde_common;
#[cfg(feature = "serde")]
pub mod de;
#[cfg(feature = "serde")]
pub mod ser;
#[cfg(feature = "dataframes")]
pub mod dataframes;

pub use format_specs::{FortField, FortFormat};
pub use fort_error::FError;
#[cfg(feature = "serde")]
pub use de::{from_str, from_str_custom, from_str_with_fields, from_str_with_fields_custom, DeSettings};
#[cfg(feature = "serde")]
pub use ser::{to_bytes, to_bytes_with_fields, to_string, to_string_with_fields, to_writer, to_writer_with_fields};
#[cfg(feature = "serde")]
pub use serde_common::{SError, DError};
#[cfg(feature = "dataframes")]
pub use dataframes::read_to_dataframe;