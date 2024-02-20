//! Serialize data according to a Fortran format string.
//! 
//! # Basic usage
//! 
//! This module expects that you have a Fortran format string, such as
//! `(a10,i3,f8.2)` and want to serialize data according to that format. 
//! The functions provided by this module belong to three groups: `to_*`,
//! `to_*_with_fields`, `to_*_custom`. The `to_*_custom` functions are the
//! most flexible but the least convenient. You only need to use them if 
//! the default [`SerSettings`] is not sufficient for your use case.
//! 
//! The distinction between the `to_*` and `to_*_with_fields` functions
//! mainly matters when serializing structures or maps. The `to_*` functions 
//! will output values in the order they are defined. That is, this example
//! will work, because the fields in `Person` are defined in the same order 
//! as they appear in the data:
//! 
//! ```
//! use fortformat::format_specs::FortFormat;
//! use fortformat::ser::to_string;
//! 
//! #[derive(Debug, PartialEq, serde::Serialize)]
//! struct Person {
//!     name: &'static str,
//!     age: i32,
//!     weight: f32,
//! }
//! 
//! let ff = FortFormat::parse("(a10,i3,f8.1)").unwrap();
//! let p = Person { name: "John Doe", age: 30, weight: 180.5 };
//! let s = to_string(p, &ff).unwrap();
//! assert_eq!(s, "  John Doe 30   180.5");
//! ```
//! 
//! However, the next example will *not* work, because the field order does not match
//! the data:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string;
//! # 
//! # #[derive(Debug, PartialEq, serde::Serialize)]
//! # struct Person {
//! #     name: String,
//! #     age: i32,
//! #     weight: f32,
//! # }
//! let ff = FortFormat::parse("(f8.1,i3,1x,a10)").unwrap();
//! let p = Person { name: "John Doe".to_string(), age: 30, weight: 180.5 };
//! let res = to_string(p, &ff);
//! assert!(res.is_err())
//! ```
//! 
//! If the order in which the fields need to be output is different from the order
//! the fields are defined in the structure, then you need to use one of the `*_with_fields`
//! functions:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string_with_fields;
//! # 
//! # #[derive(Debug, PartialEq, serde::Serialize)]
//! # struct Person {
//! #     name: String,
//! #     age: i32,
//! #     weight: f32,
//! # }
//! let ff = FortFormat::parse("(f8.1,i3,a10)").unwrap();
//! let p = Person { name: "John Doe".to_string(), age: 30, weight: 180.5 };
//! let fields = ["weight", "age", "name"];
//! let s = to_string_with_fields(p, &ff, &fields).unwrap();
//! assert_eq!(s, "   180.5 30  John Doe");
//! ```
//! 
//! **Note: take special care with maps.** Most maps do not guarantee
//! the order their values are visited, so using one of the serialization
//! functions that doesn't take field names will usually result in undetermined
//! order in which the data are written out.
//! 
//! # Serializing nested structures
//! 
//! Since Fortran formatted data does not have a way to represent nesting, this
//! can be a little tricky. If relying on the order of structure fields, then you
//! do not need to do anything special - the serializer will correctly recognize
//! that only the bool, int, float, char, and str/String fields map to format
//! fields:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string;
//! 
//! #[derive(Debug, PartialEq, serde::Serialize)]
//! struct SiteInfo {
//!     name: String,
//!     coords: Coordinates
//! }
//! 
//! #[derive(Debug, PartialEq, serde::Serialize)]
//! struct Coordinates {
//!     longitude: f32,
//!     latitude: f32,
//! }
//! 
//! let site = SiteInfo { 
//!     name: "Ferris Island".to_string(),
//!     coords: Coordinates { longitude: 1.0, latitude: -5.5 }
//! };
//! 
//! let ff = FortFormat::parse("(a15,2f5.1)").unwrap();
//! let s = to_string(&site, &ff).unwrap();
//! assert_eq!(s, "  Ferris Island  1.0 -5.5");
//! ```
//! 
//! However, the following example will return an error from the `to_string` function:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string_with_fields;
//! # 
//! # #[derive(Debug, PartialEq, serde::Serialize)]
//! # struct SiteInfo {
//! #     name: String,
//! #     coords: Coordinates
//! # }
//! # 
//! # #[derive(Debug, PartialEq, serde::Serialize)]
//! # struct Coordinates {
//! #     longitude: f32,
//! #     latitude: f32,
//! # }
//! 
//! let site = SiteInfo { 
//!     name: "Ferris Island".to_string(),
//!     coords: Coordinates { longitude: 1.0, latitude: -5.5 }
//! };
//! 
//! let ff = FortFormat::parse("(a15,2f5.1)").unwrap();
//! let fields = ["latitude", "longitude", "name"];
//! let res = to_string_with_fields(&site, &ff, &fields);
//! assert!(res.is_err());
//! ```
//! 
//! Specifically, you would see an error that the "coords" field is missing.
//! That is because, without the clue from the `#[serde(flatten)]` attribute
//! that `coords` will not be one of the Fortran fields, the serializer can't
//! tell that ahead of time. Adding `#[serde(flatten)]` to the `coords` field
//! will fix this:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string_with_fields;
//! 
//! #[derive(Debug, PartialEq, serde::Serialize)]
//! struct SiteInfo {
//!     name: String,
//!     #[serde(flatten)]
//!     coords: Coordinates
//! }
//! 
//! #[derive(Debug, PartialEq, serde::Serialize)]
//! struct Coordinates {
//!     longitude: f32,
//!     latitude: f32,
//! }
//! 
//! let site = SiteInfo { 
//!     name: "Ferris Island".to_string(),
//!     coords: Coordinates { longitude: 1.0, latitude: -5.5 }
//! };
//! 
//! let ff = FortFormat::parse("(2f5.1,a15)").unwrap();
//! let fields = ["latitude", "longitude", "name"];
//! let s = to_string_with_fields(&site, &ff, &fields).unwrap();
//! assert_eq!(s, " -5.5  1.0  Ferris Island");
//! ```
//! 
//! You can also use `#[serde(flatten)]` on maps:
//! 
//! ```
//! # use std::collections::HashMap;
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string_with_fields;
//! 
//! #[derive(Debug, PartialEq, serde::Serialize)]
//! struct SiteInfo {
//!     name: String,
//!     #[serde(flatten)]
//!     concentrations: HashMap<&'static str, f32>
//! }
//! 
//! let concentrations = HashMap::from([
//!     ("co2", 413.5),
//!     ("ch4", 1899.3),
//! ]);
//! 
//! let site = SiteInfo{ name: "Mauna Loa".to_string(), concentrations };
//! let ff = FortFormat::parse("(a12,10f8.1)").unwrap();
//! let fields = ["name", "co2", "ch4"];
//! let s = to_string_with_fields(&site, &ff, &fields).unwrap();
//! assert_eq!(s, "   Mauna Loa   413.5  1899.3");
//! ```
//! 
//! Note in this last example that the number of fields in the format string, `(a12,10f8.1)`,
//! is larger than the number of fields actually written. This is fine, and is a useful way
//! to provide a format string that can handle a sequence of an unknown length as the last
//! thing to be serialized: just make the format string long enough to cover the largest
//! possible number of elements.
//! 
//! # Field names, tuples, vectors, or other sequences
//! 
//! If using field names, there must be one for each concrete value serialized. Consider
//! this example:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string_with_fields;
//! 
//! #[derive(Debug, PartialEq, serde::Serialize)]
//! struct Coordinates {
//!     longitude: f32,
//!     latitude: f32,
//! }
//! 
//! let value = ("Ferris Island", Coordinates{ longitude: 1.0, latitude: -5.5 });
//! let ff = FortFormat::parse("(a13,1x,f5.1,f5.1)").unwrap();
//! let fields = ["latitude", "longitude"];
//! let res = to_string_with_fields(value, &ff, &fields);
//! assert!(res.is_err());
//! ```
//! 
//! This fails because although "latitude" and "longitude" are our only two named fields
//! in `Coordinates`, the serializer needs one field name for each non-positional format
//! spec in the format string. (Positional specs are ones like `x` that add space but
//! do not represent a value.) Here, the string that is the first tuple element must have
//! a field, even if it is a placeholder. The following will work:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string_with_fields;
//! # 
//! # #[derive(Debug, PartialEq, serde::Serialize)]
//! # struct Coordinates {
//! #     longitude: f32,
//! #     latitude: f32,
//! # }
//! # 
//! let value = ("Ferris Island", Coordinates{ longitude: 1.0, latitude: -5.5 });
//! let ff = FortFormat::parse("(a13,1x,f5.1,f5.1)").unwrap();
//! let fields = ["", "latitude", "longitude"];
//! let s = to_string_with_fields(value, &ff, &fields).unwrap();
//! assert_eq!(s, "Ferris Island  -5.5  1.0");
//! ```
//! 
//! Another potentially confusing case is when you have a vector of the same structure
//! repeated and you pass field names. In the example below, you might expect that the
//! serializer could get mixed up by the repeated field names. However, this works
//! correctly:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string_with_fields;
//! # 
//! # #[derive(Debug, PartialEq, serde::Serialize)]
//! # struct Coordinates {
//! #     longitude: f32,
//! #     latitude: f32,
//! # }
//! let value = vec![
//!     Coordinates{ longitude: 1.0, latitude: -5.5 },
//!     Coordinates{ longitude: -45.0, latitude: 60.0 }
//! ];
//! let ff = FortFormat::parse("(4f6.1)").unwrap();
//! let fields = ["latitude", "longitude", "latitude", "longitude"];
//! let s = to_string_with_fields(value, &ff, &fields).unwrap();
//! 
//! assert_eq!(s, "  -5.5   1.0  60.0 -45.0");
//! ```
//! 
//! The reason is that the serializer internally tracks which fields it has written
//! and always uses the next field with the correct name. So in this example the process
//! is:
//! 
//! 1. Take the first element of `value`, it is a struct, so take the first field `longitude`.
//! 2. We have not yet serialized any values, so our format and field indices both are 0.
//! 3. Starting from `fields[0]` find the first index where our current struct field, "longitude",
//!    is present. This is index 1, so serialize the value using the format spec at index 1 and hold
//!    this in memory.
//!    (If positional format specs like `1x` are present, they are ignored while counting the index.)
//! 4. Repeat for the other field on our field element. 
//! 5. The first struct is fully serialized, write the bytes in the proper order (latitude first, them
//!    longitude.)
//! 6. Since we serialized two fields, increment the field and format index by 2.
//! 7. Take the second element of `value`, which is also a struct, and take its first field `longitude`.
//! 8. Look for where "longitude" shows up in the list of `fields`, *starting from index 2*. This is at
//!    index 3, so the longitude value will be serialized using the format at index 3 and written to the
//!    corresponding position in the output.
//! 
//! At present, there is no way to tell it to "loop" the field names (i.e. you cannot pass just
//! `["latitude", "longitude"]` for `fields` in the above example - it must have 4 elements matching
//! 4 total fields).
//! 
//! # Strings and the format spec
//! 
//! The Fortran `CHARACTER` type is essentially an alias for `byte`, as Fortran was not
//! designed with multi-byte characters in mind. Thus, the character format `aN` means
//! that field can only hold *N* bytes, which may be fewer than *N* Unicode characters.
//! If your output strings contain non-ASCII characters and are being unexpectedly truncated,
//! this could be why.
//! 
//! # Enum variants and the format spec
//! 
//! Enum variants can be identified either by their name or index. This crate allows either,
//! and will automatically select which one to use based on the format string:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string;
//! #[derive(serde::Serialize)]
//! enum Test {
//!     Alpha,
//!     Beta
//! }
//! 
//! // If the format spec for the variant is an integer, then the
//! // variant index will be written.
//! let value = [Test::Alpha, Test::Beta];
//! let ff1 = FortFormat::parse("(i1,1x,i1)").unwrap();
//! let s1 = to_string(&value, &ff1).unwrap();
//! assert_eq!(s1, "0 1");
//! 
//! // If the format spec for the variant is a character array,
//! // then the format name is written instead.
//! let ff2 = FortFormat::parse("(a5,1x,a5)").unwrap();
//! let s2 = to_string(&value, &ff2).unwrap();
//! assert_eq!(s2, "Alpha  Beta");
//! ```
//! 
//! Variants containing values are also supported, but will run into the limits of Fortran
//! formatted output. Given an enum whose variants both contain a similar type:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string;
//! #[derive(serde::Serialize)]
//! enum Test {
//!     Alpha(i32),
//!     Beta(u16)
//! }
//! 
//! let value = [Test::Alpha(-99), Test::Beta(42)];
//! let ff = FortFormat::parse("2(a5,1x,i4,1x)").unwrap();
//! let s = to_string(&value, &ff).unwrap();
//! assert_eq!(s, "Alpha  -99  Beta   42");
//! ```
//! 
//! this will work for any value of `Test`, because both variants can be serialized as the
//! variant name (or index) and an integer value. However, if you had an enum like:
//! 
//! ```no_run
//! enum InstrumentValue {
//!     Nothing,
//!     Value(f32),
//!     ValueWithError(f32, f32)
//! }
//! ```
//! 
//! it's clear that the different variants correspond to different formats, e.g.:
//! 
//! - `Nothing` = `(a14)`
//! - `Value` = `(a14,f13.5)`
//! - `ValueWithError` = `(a14,f13.5,f13.5)`
//! 
//! One way way around this would be to use the `into` attribute to tell serde
//! to convert the enum into some type with a common representation
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::to_string;
//! #[derive(Debug, Clone, serde::Serialize)]
//! #[serde(into = "(&'static str, f32, f32)")]
//! enum InstrumentValue {
//!     Nothing,
//!     Value(f32),
//!     ValueWithError(f32, f32)
//! }
//! 
//! // Convert the enum into its name and two floats - even if the variant
//! // doesn't have two floats. Use a fill value for the float(s) not present.
//! impl From<InstrumentValue> for (&'static str, f32, f32) {
//!     fn from(value: InstrumentValue) -> Self {
//!         match value {
//!             InstrumentValue::Nothing => ("Nothing", -999.0, -999.0),
//!             InstrumentValue::Value(v) => ("Value", v, -999.0),
//!             InstrumentValue::ValueWithError(v, e) => ("Val+Err", v, e),
//!         }
//!     }
//! }
//! 
//! let values = [
//!     InstrumentValue::Nothing,
//!     InstrumentValue::Value(1.0),
//!     InstrumentValue::ValueWithError(2.0, 0.2)
//! ];
//! 
//! // Because we included the #[serde(into = "...")] attribute on the enum,
//! // when serde goes to serialize it, it first gets converted to a string
//! // and two floats, and those are serialized. This allows us to use
//! // (a7,f8.3,f8.3) for any variant.
//! let ff = FortFormat::parse("(3(a7,1x,f8.3,1x,f8.3,1x))").unwrap();
//! let s = to_string(values, &ff).unwrap();
//! 
//! assert_eq!(s, "Nothing -999.000 -999.000   Value    1.000 -999.000 Val+Err    2.000    0.200");
//! ```
//! 
//! If you need to be able to deserialize such a value, you would probably also want to include the
//! `#[serde(try_from = "...")]` attribute.
//! 
//! ## Enum representations
//! 
//! For now, the different representations of enums are partially supported, but will all return the
//! same result. Using internal or adjacent tagging on types passed to one of the `*_with_fields` 
//! functions will not correctly place the tag value in the correct place given the field names.
//! That is, given the following example:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::ser::{to_string,to_string_with_fields};
//! #[derive(Debug, serde::Serialize)]
//! #[serde(tag = "type")]
//! enum Internal {
//!     Alpha{value: i32},
//!     Beta{value: i32},
//! }
//! 
//! let in_vec = vec![Internal::Alpha{value: 12}, Internal::Beta{value: 24}];
//! let in_ff = FortFormat::parse("(2(a6,i3))").unwrap();
//! let in_s = to_string(&in_vec, &in_ff).unwrap();
//! assert_eq!(in_s, " Alpha 12  Beta 24");
//! 
//! let fields = ["type", "value"];
//! let ff = FortFormat::parse("(i2,1x,a5)").unwrap();
//! let res = to_string_with_fields(
//!     Internal::Alpha { value: 42 },
//!     &ff,
//!     &fields
//! );
//! assert!(res.is_err());
//! ```
//! 
//! you will get an error because it still tries to serialize the variant first. This is not
//! the desired behavior, and may be fixed in a future version.
//! 
//! # None and unit types
//! 
//! Since Fortran does not have a good way to represent types containing no data, there was not an
//! single, clear way to handle `None` values, the unit `()`, and unit structures (e.g. structures
//! with no values inside them). Our current approach is to write all of these types as fill values.
//! The logic was:
//! 
//! 1. Fill values are the closest thing to an "optional" type in Fortran, so are the least bad way
//!    to communicate a `None` value.
//! 2. Unit types still need a valid placeholder to fill their space in the text input/output, so
//!    again a fill value is the least bad way to handle this.
//! 
//! The default "fill value" mimics Fortran's behavior when a value overflows its field width - 
//! in such a case, the field is filled with `*`s. Since such a value is interpreted by Fortran
//! as a non-number (for numeric fields), this is again the least-bad default in our opinion.
//! You can change how fill values are generated using one of the `*_custom` methods with a
//! [`SerSettings`] instance. Fill value format is defined by a [`NoneFill`] enum contained
//! in [`SerSettings`]; see the [`NoneFill`] documentation for the available choices.
use std::{fmt::{Octal, UpperHex}, io::Write, rc::Rc, string::FromUtf8Error};

use ryu_floating_decimal::d2d;
use serde::ser;
use crate::{de::FortFormat, format_specs::{FortField, IntBase, RealFmt}, serde_common::{NoneFill, SError, SResult}};

/// Serialize a value into a string using the given Fortran format.
/// 
/// When serializing structures or maps using this function, the order of the fields
/// or values is the order in which they will be serialized. This must match the order
/// of the type specifications in the format. Note that because most map types do not
/// provide a consistent order, it is therefore not recommended to use this function
/// when serializing a map or anything containing a map. Use [`to_string_with_fields`]
/// instead.
/// 
/// In addition to erroring if the serialization fails (see [`to_bytes`] for possible
/// causes), this function will error in the unlikely case where the serialized bytes
/// cannot be interpreted as valid UTF-8.
pub fn to_string<T>(value: T, fmt: &FortFormat) -> SResult<String> 
where T: ser::Serialize
{
    let mut serializer = Serializer::new(fmt);
    value.serialize(&mut serializer)?;
    Ok(serializer.try_into_string()?)
}

/// Serialize a value into a string using the given Fortran format and a list of field names.
/// 
/// When serializing a structure or map, the fields/values will be written out in the order
/// that their names appear in `fields`. (For maps with non-string keys, the serialized version
/// of each key is matched against `fields`.) See the module-level documentation for how this
/// works when a struct/map is part of a tuple.
/// 
/// Like [`to_string`], this will return an error if serialization fails or if the resulting
/// bytes cannot be converted to UTF-8.
pub fn to_string_with_fields<T>(value: T, fmt: &FortFormat, fields: &[&str]) -> SResult<String> 
where T: ser::Serialize
{
    let mut serializer = Serializer::new_with_fields(fmt, fields);
    value.serialize(&mut serializer)?;
    Ok(serializer.try_into_string()?)
}

/// Serialize a value into a string with full control over how the serialization is done.
/// 
/// Use this method if you need to pass custom settings. See [`SerSettings`] for available
/// options. Pass `None` for `fields` if there are no field names to match up.
pub fn to_string_custom<T>(value: T, fmt: &FortFormat, fields: Option<&[&str]>, settings: SerSettings) -> SResult<String> 
where T: ser::Serialize
{
    let mut serializer = Serializer::new_custom(fmt, fields, settings);
    value.serialize(&mut serializer)?;
    Ok(serializer.try_into_string()?)
}

/// Serialize a value into a sequence of bytes using the given Fortran format.
/// 
/// This is the same as [`to_string`], except the resulting bytes are directly
/// returned, rather than being converted to UTF-8 first. If you don't need
/// a string, this avoids the possible error from non-UTF8 bytes.
/// 
/// This function will return an error if serialization fails. Some common reasons
/// for this are:
/// 
/// - The next Rust type does not match the next Fortran type in the format spec.
/// - The type `T` has nested structures (a struct with another struct or map as a field)
///   and does not use the `#[serde(flatten)]` attribute on the nested struct or map.
/// - The format spec is too short, and ends before the values to be serialized do.
/// 
/// These cases are represented by the variants of [`SError`].
pub fn to_bytes<T>(value: T, fmt: &FortFormat) -> SResult<Vec<u8>> 
where T: ser::Serialize    
{
    let mut serializer = Serializer::new(fmt);
    value.serialize(&mut serializer)?;
    Ok(serializer.into_bytes())
}

/// Serialize a value into a sequence of bytes using the given Fortran format and a list of field names.
/// 
/// This works identically to [`to_string_with_fields`] except the serialized bytes are returned directly,
/// rather than being converted to a UTF-8 string.
/// 
/// An additional reason compared to [`to_bytes`] that this function might error is if the list of field
/// names is shorter than the number of concrete values to serialize.
pub fn to_bytes_with_fields<T>(value: T, fmt: &FortFormat, fields: &[&str]) -> SResult<Vec<u8>> 
where T: ser::Serialize    
{
    let mut serializer = Serializer::new_with_fields(fmt, fields);
    value.serialize(&mut serializer)?;
    Ok(serializer.into_bytes())
}

/// Serialize a value into a sequence of bytes with full control over how the serialization is done.
/// 
/// Use this method if you need to pass custom settings. See [`SerSettings`] for available
/// options. Pass `None` for `fields` if there are no field names to match up.
pub fn to_bytes_custom<T>(value: T, fmt: &FortFormat, fields: Option<&[&str]>, settings: SerSettings) -> SResult<Vec<u8>> 
where T: ser::Serialize    
{
    let mut serializer = Serializer::new_custom(fmt, fields, settings);
    value.serialize(&mut serializer)?;
    Ok(serializer.into_bytes())
}

/// Serialize a value directly to a writer using the given Fortran format.
/// 
/// This is a more convenient way to write to e.g. a file than using [`to_bytes`]
/// to get the byte array first, and writing that. Other than requiring an
/// object that implements [`std::io::Write`] to be passed in, this is otherwise
/// identical to [`to_bytes`].
/// 
/// In addition to possible serialization errors, this will return an error if
/// writing fails.
/// 
/// # Notes:
/// 
/// 1. It is *strongly* encouraged to use some form of buffered writer
///    for `writer`, as the serializer often writes single bytes due to the
///    need to match Fortran-style numbers. Without buffering, this could result
///    in very slow output.
/// 2. Often in Fortran a format spec will represent one data record and there
///    will be one data record per line. This method does *not* automatically
///    add a newline at the end of a record; you will need to do so by calling
///    `writer.write(b"\n")` or something equivalent.
pub fn to_writer<T, W>(value: T, fmt: &FortFormat, writer: W) -> SResult<()> 
where
    T: ser::Serialize,
    W: Write
{
    let mut serializer = Serializer::new_writer(fmt, writer);
    value.serialize(&mut serializer)?;
    Ok(())
}

/// Serialize a value directly to a writer using the given Fortran format and a list of field names.
/// 
/// This is the equivalent of [`to_bytes_with_fields`] but writes directly to something
/// implementing [`std::io::Write`]. The same notes given for [`to_writer`] apply.
pub fn to_writer_with_fields<T, W>(value: T, fmt: &FortFormat, fields: &[&str], writer: W) -> SResult<()> 
where
    T: ser::Serialize,
    W: Write
{
    let mut serializer = Serializer::new_writer_with_fields(fmt, fields, writer);
    value.serialize(&mut serializer)?;
    Ok(())
}

/// Serialize a value directly to a writer with full control over how the serialization is done.
/// 
/// Use this method if you need to pass custom settings. See [`SerSettings`] for available
/// options. Pass `None` for `fields` if there are no field names to match up.
pub fn to_writer_custom<T, W>(value: T, fmt: &FortFormat, fields: Option<&[&str]>, settings: SerSettings, writer: W) -> SResult<()> 
where
    T: ser::Serialize,
    W: Write
{
    let mut serializer = Serializer::new_writer_custom(fmt, fields, settings, writer);
    value.serialize(&mut serializer)?;
    Ok(())
}

/// Settings for serialization.
/// 
/// This can be used with the `*_custom` methods to change how the serialization
/// behaves. To construct, call `SerSettings::default()` to build the default,
/// then use the various methods to update the settings, e.g.:
/// 
/// ```
/// # use fortformat::ser::SerSettings;
/// # use fortformat::serde_common::NoneFill;
/// let settings = SerSettings::default()
///     .fill_method(NoneFill::new_string("N/A"));
/// ```
/// 
/// Each of the methods' documentation describes the purpose of its setting
/// and the default.
#[derive(Debug, Default)]
pub struct SerSettings {
    fill_method: NoneFill,
}

impl SerSettings {
    /// Sets how `None` values, the unit type, and unit structs are written.
    /// 
    /// The default is the default [`NoneFill`], which is to write an "*" for
    /// the full width of the field.
    pub fn fill_method(mut self, fill_method: NoneFill) -> Self {
        self.fill_method = fill_method;
        self
    }
}

#[derive(Debug, Default)]
struct MapSerHelper {
    next_field_index: Option<usize>,
    next_field_fmt: Option<FortField>,
    data: Vec<Option<Vec<u8>>>,
    in_use: bool
}

impl MapSerHelper {
    fn take_validate_data(&mut self) -> Vec<Option<Vec<u8>>> {
        let data = std::mem::take(&mut self.data);
        self.next_field_fmt = None;
        self.next_field_index = None;
        self.in_use = false;
        data
    }
}

/// Serializer for Fortran-format writers
struct Serializer<'f, W: Write> {
    buf: W,
    fmt: &'f FortFormat,
    fmt_idx: usize,
    fields: Option<&'f[ &'f str]>,
    field_idx: usize,
    map_helper: MapSerHelper,
    settings: SerSettings,
}

impl<'f> Serializer<'f, Vec<u8>> {
    pub fn new(fmt: &'f FortFormat) -> Self {
        Self { buf: vec![], fmt, fmt_idx: 0, fields: None, field_idx: 0, map_helper: MapSerHelper::default(), settings: SerSettings::default() }
    }

    pub fn new_with_fields(fmt: &'f FortFormat, fields: &'f[&'f str]) -> Self {
        Self { buf: vec![], fmt, fmt_idx: 0, fields: Some(fields), field_idx: 0, map_helper: MapSerHelper::default(), settings: SerSettings::default() }
    }

    pub fn new_custom(fmt: &'f FortFormat, fields: Option<&'f[&'f str]>, settings: SerSettings) -> Self {
        Self { buf: vec![], fmt, fmt_idx: 0, fields, field_idx: 0, map_helper: MapSerHelper::default(), settings }
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.buf.to_vec()
    }

    pub fn try_into_string(self) -> Result<String, FromUtf8Error> {
        String::from_utf8(self.buf)
    }
}

impl <'f, W: Write> Serializer<'f, W> {
    pub fn new_writer(fmt: &'f FortFormat, writer: W) -> Self {
        Self { buf: writer, fmt, fmt_idx: 0, fields: None, field_idx: 0, map_helper: MapSerHelper::default(), settings: SerSettings::default() }
    }

    pub fn new_writer_with_fields(fmt: &'f FortFormat, fields: &'f[&'f str], writer: W) -> Self {
        Self { buf: writer, fmt, fmt_idx: 0, fields: Some(fields), field_idx: 0, map_helper: MapSerHelper::default(), settings: SerSettings::default() }
    }

    pub fn new_writer_custom(fmt: &'f FortFormat, fields: Option<&'f[&'f str]>, settings: SerSettings, writer: W) -> Self {
        Self { buf: writer, fmt, fmt_idx: 0, fields: fields, field_idx: 0, map_helper: MapSerHelper::default(), settings }
    }
}

impl<'f, W: Write + 'f> Serializer<'f, W> {
    // This shares a lot of code with the Deserializer. I tried refactoring that out
    // into an inner struct, but that ended up being more awkward because the inner
    // struct didn't know about the Deserializer's input string. Another option
    // might be a trait that requires defining advance_over_skips and methods
    // to increment indices and get formats/field names - will explore later.

    fn advance_over_skips(&mut self) -> std::io::Result<()> {
        loop {
            // Consume any skips (i.e. 1x, 2x) in the format, also adding space
            // to the output. This can be modified to handle other types
            // of Fortran positioning formats in the future.
            let peeked_fmt = self.fmt.fields.get(self.fmt_idx);
            match peeked_fmt {
                Some(&FortField::Skip) => {
                    self.buf.write(b" ")?;
                    self.fmt_idx += 1;
                }
                _ => return Ok(()),
            }
        }
    }

    fn next_fmt(&mut self) -> SResult<&FortField> {
        self.advance_over_skips()?;
        loop {
            let next_fmt = self.fmt.fields.get(self.fmt_idx);
            match next_fmt {
                Some(field) => {
                    self.fmt_idx += 1;
                    self.field_idx += 1;
                    return Ok(field)
                },
                None => return Err(SError::FormatSpecTooShort)
            }
        }
    }

    fn curr_field(&mut self) -> Option<&str> {
        if let Some(fields) = self.fields {
            fields.get(self.field_idx).map(|f| *f)
        } else {
            panic!("Called next_field on a deserializer without fields")
        }
    }

    fn try_prev_field(&self) -> Option<&str> {
        if self.field_idx == 0 {
            return None;
        }

        self.fields.map(|f| f.get(self.field_idx - 1))
            .flatten()
            .map(|f| *f)
    }

    fn peek_fmt(&mut self) -> Option<&FortField> {
        // We don't use advance_over_skips() here because that writes
        // things to the buffer, which a peek shouldn't do (and which
        // might fail).
        let mut i = self.fmt_idx;
        loop {
            let fmt = self.fmt.fields.get(i)?;
            if !fmt.is_positional() {
                return Some(fmt);
            }
            i += 1;
        }
    }

    fn get_nth_nonskip_fmt(&self, n: usize) -> Option<&FortField> {
        let mut i = 0;
        let mut j = 0;
        loop {
            let fmt = self.fmt.fields.get(j)?;
            if !fmt.is_positional() && i == n {
                return Some(fmt)
            } else if !fmt.is_positional() {
                i += 1;
            }
            j += 1;
        }
    }

    fn get_fmt_and_index_offset_for_field(&self, field_name: &str) -> Option<(usize, FortField)> {
        if let Some(fields) = self.fields {
            let mut i = 0;
            for &fname in &fields[self.field_idx..] {
                if field_name == fname {
                    let fmt = self.get_nth_nonskip_fmt(self.field_idx + i)?;
                    return Some((i, *fmt));
                }
                i += 1;
            }
            None
        } else {
            panic!("Called get_fmt_and_index_offset_for_field on a serializer without field names");
        }
    }

    /// Write an existing slice of bytes to the buffer and advance the internal pointer to the
    /// next format and field name.
    /// 
    /// # Panics
    /// Panics if the input slice does not have the number of bytes expected for the next format.
    /// It is the caller's responsibility to ensure that the correct number of bytes are provided.
    fn write_next_entry_raw(&mut self, bytes: &[u8], fmt: Option<FortField>) -> SResult<()> {
        let fmt = if let Some(fmt) = fmt {
            fmt
        } else {
            self.advance_over_skips()?;
            *self.next_fmt()?
        };

        let nbytes = match fmt {
            FortField::Char { width } => width,
            FortField::Logical { width } => Some(width),
            FortField::Integer { width, zeros: _, base: _ } => Some(width),
            FortField::Real { width, precision: _, fmt: _, scale: _ } => Some(width),
            FortField::Skip => panic!("Should not get a skip format, should have advanced over all skips"),
        };

        if let Some(n) = nbytes {
            if n != bytes.len() as u32 {
                panic!("Called write_next_entry_raw with a slice of {} bytes, expected a slice of {} bytes", bytes.len(), n);
            }
        }

        self.buf.write(bytes)?;
        Ok(())
    }

    fn serialize_integer<I: itoa::Integer + Octal + UpperHex>(&mut self, abs_value: I, is_neg: bool) -> SResult<()> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Integer { width, zeros, base } = next_fmt {
            serialize_integer(width, zeros, base, &mut self.buf, abs_value, is_neg)
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "integer", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn serialize_real(&mut self, v: f64) -> SResult<()> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Real { width, precision, fmt, scale } = next_fmt {
            let precision = precision.ok_or_else(|| SError::InvalidOutputFmt(
                next_fmt, "real number formats must include a precision for output".to_string()
            ))?;

            // TODO: apparently E and D formats can specify the number of digits in the exponent, that will
            // need added to the format spec.
            match fmt {
                RealFmt::D => serialize_real_exp(&mut self.buf, v, width, precision, scale, "D", None),
                RealFmt::E => serialize_real_exp(&mut self.buf, v, width, precision, scale, "E", None),
                RealFmt::F => serialize_real_f(&mut self.buf, v, width, precision, scale),
                RealFmt::G => todo!(),
            }
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "float", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn serialize_key_helper(&mut self, field: &str) -> SResult<()> {
        if self.fields.is_some() {
            let (offset, fmt) = self.get_fmt_and_index_offset_for_field(field)
                .ok_or_else(|| SError::FieldMissingError(field.to_string()))?;
            self.map_helper.next_field_index = Some(offset);
            self.map_helper.next_field_fmt = Some(fmt);
            Ok(())
        } else {
            Ok(())
        }
    }

    fn serialize_value_helper<T: ?Sized>(&mut self, value: &T) -> SResult<()>
    where
        T: serde::Serialize {
        if self.fields.is_none() {
            return value.serialize(&mut *self);
        }

        if let (Some(offset), Some(fmt)) = (self.map_helper.next_field_index, self.map_helper.next_field_fmt) {
            while self.map_helper.data.len() <= offset {
                self.map_helper.data.push(None);
            }

            // TODO: I don't think this will work for fields that are themselves structures or maps. Will need
            // to iterate.
            let fortfmt = FortFormat{ fields: vec![fmt] };
            let bytes = to_bytes(value, &fortfmt)?;
            self.map_helper.data[offset] = Some(bytes);
        } else {
            panic!("serialize_key must be called before serialize_value when field names are given.");
        }

        Ok(())
    }

    fn end_helper(&mut self) -> SResult<()> {
        if self.map_helper.next_field_index.is_some() {
            for maybe_bytes in self.map_helper.take_validate_data() {
                if let Some(bytes) = maybe_bytes {
                    self.write_next_entry_raw(&bytes, None)?;
                } else {
                    let field_name = self.curr_field().unwrap_or("?");
                    unimplemented!("The field {field_name} did not have a value, but a later field did. This is not handled yet.");
                }
            }
        }
        Ok(())
        
    }
}


impl<'a, 'f, W: Write + 'f> ser::Serializer for &'a mut Serializer<'f, W> {
    type Ok = ();
    type Error = SError;

    // we already store the format information on this struct so we should
    // be able to just use it for all the sequence serialization.
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Logical { width } = next_fmt {
            serialize_logical(v, width, &mut self.buf)
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "bool", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        self.serialize_real(v as f64)
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        self.serialize_real(v)
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(&v.to_string())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        self.serialize_bytes(v.as_bytes())
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Char { width } = next_fmt {
            serialize_characters(v, width, &mut self.buf)
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "char/str/bytes", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        let next_fmt = *self.next_fmt()?;
        let fill_bytes = self.settings.fill_method.make_fill_bytes(&next_fmt)?;
        self.write_next_entry_raw(&fill_bytes, Some(next_fmt))
    }

    fn serialize_some<T: ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: serde::Serialize {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        self.serialize_none()
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        self.serialize_none()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        // Since Fortran specifies which type each field should be, we can determine whether to serialize
        // as an integer or string.
        // TODO: add deserialization to allow round-tripping.
        let peeked_fmt = *self.peek_fmt().ok_or_else(|| SError::FormatSpecTooShort)?;
        if let FortField::Integer { width: _, zeros: _, base: _ } = peeked_fmt {
            self.serialize_u32(variant_index)
        } else if let FortField::Char { width: _ } = peeked_fmt {
            self.serialize_str(variant)
        } else {
            Err(SError::FormatTypeMismatch { spec_type: peeked_fmt, serde_type: "str or integer", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }

    }

    fn serialize_newtype_struct<T: ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: serde::Serialize {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T: ?Sized>(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: serde::Serialize {
        // Consider this behavior subject to change, but it seems that the most sensible
        // way to serialize a variant is to put the index/variant in the first field and
        // the value in the second.
        self.serialize_unit_variant(name, variant_index, variant)?;
        value.serialize(self)
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(self)
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(self)
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Ok(self)
    }

    fn serialize_tuple_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        self.serialize_unit_variant(name, variant_index, variant)?;
        Ok(self)
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        if self.map_helper.in_use {
            unimplemented!("Can't yet recursively call serialize_map - the map_helper must be reset before the next call")
        }
        Ok(self)
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        if self.map_helper.in_use {
            unimplemented!("Can't yet recursively call serialize_map - the map_helper must be reset before the next call")
        }
        Ok(self)
    }

    fn serialize_struct_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        if self.map_helper.in_use {
            unimplemented!("Can't yet recursively call serialize_map - the map_helper must be reset before the next call")
        }
        self.serialize_unit_variant(name, variant_index, variant)?;
        Ok(self)
    }
}

impl<'a, 'f, W: Write + 'f> ser::SerializeSeq for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        // From a serialization standpoint, we just serialize each value in a sequence
        // as normal, we cannot indicate that these elements are grouped together.
        value.serialize(&mut **self)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<'a, 'f, W: Write + 'f> ser::SerializeTuple for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        // From a serialization standpoint, we just serialize each value in a tuple
        // as normal, we cannot indicate that these elements are grouped together.
        // (Same as for a sequence.)
        value.serialize(&mut **self)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<'a, 'f, W: Write + 'f> ser::SerializeTupleStruct for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        // From a serialization standpoint, we just serialize each value in a tuple
        // struct as normal, we cannot indicate that these elements are grouped together.
        // (Same as for a sequence.)
        value.serialize(&mut **self)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<'a, 'f, W: Write + 'f> ser::SerializeTupleVariant for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        // From a serialization standpoint, we just serialize each value in a tuple
        // variant as normal, we cannot indicate that these elements are grouped together.
        // (Same as for a sequence.)
        value.serialize(&mut **self)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}


impl<'a, 'f, W: Write + 'f> ser::SerializeMap for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        if self.fields.is_some() {
            // This is weird, but since all we know about key is that it is serializable
            // the best we can do is serialize it to a string and check against the field
            // names
            let fmt = FortFormat::parse("(a512)").unwrap();
            let key_string = to_string(key, &fmt)
                .map_err(|e| SError::KeyToFieldError(Rc::new(e)))?;
            self.serialize_key_helper(key_string.trim())
        } else {
            Ok(())
        }
    }

    fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        self.serialize_value_helper(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        self.end_helper()
    }
}

// This will have to be a different structure; if it has known fields, then
// this will have to build a Vec<Vec<u8>> to put the elements in the correct
// order and write that to the buffer at the end. Same of SerializeMap.
impl<'a, 'f, W: Write + 'f> ser::SerializeStruct for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_field<T: ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        if self.fields.is_some() {
            self.serialize_key_helper(key)?;
        }
        self.serialize_value_helper(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        self.end_helper()
    }
}

impl<'a, 'f, W: Write + 'f> ser::SerializeStructVariant for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_field<T: ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        if self.fields.is_some() {
            self.serialize_key_helper(key)?;
        }
        self.serialize_value_helper(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        self.end_helper()
    }
}

pub(crate) fn serialize_logical<W: Write>(v: bool, width: u32, mut buf: W) -> SResult<()> {
    let b = if v { b"T" } else { b"F" };
    for _ in 0..width-1 {
        buf.write(b" ")?;
    }
    buf.write(b)?;
    Ok(())
}

pub(crate) fn serialize_characters<W: Write>(v: &[u8], width: Option<u32>, mut buf: W) -> SResult<()> {
    if let Some(width) = width {
        let w = width as usize;
        if v.len() >= w {
            buf.write(&v[..w])?;
        } else {
            for _ in 0..(w - v.len()) {
                buf.write(b" ")?;
            }
            buf.write(v)?;
        }
        Ok(())
    } else {
        // With no width specified, the full string is written out with its exact length.
        buf.write(v)?;
        Ok(())
    }
}

pub(crate) fn serialize_integer<W: Write, I: itoa::Integer + Octal + UpperHex>(
    width: u32,
    zeros: Option<u32>,
    base: IntBase,
    mut buf: W, 
    abs_value: I, 
    is_neg: bool
) -> SResult<()> {
    // wish that this didn't require allocating a vector, but I think this is the cleanest way
    // to handle this, since we need to know the length of the serialized number before we
    // can write.
    let (s, is_dec): (Vec<u8>, bool) = match base {
        IntBase::Decimal => {
            let mut b = itoa::Buffer::new();
            (b.format(abs_value).as_bytes().into_iter().copied().collect(), true)
        },
        IntBase::Octal => {
            (format!("{abs_value:o}").as_bytes().into_iter().copied().collect(), false)
        },
        IntBase::Hexadecimal => {
            (format!("{abs_value:X}").as_bytes().into_iter().copied().collect(), false)
        },
    };
    

    let nsign = if is_neg { 1 } else { 0 };
    let nzeros = zeros.map(|n| n.saturating_sub(s.len() as u32)).unwrap_or(0);
    let nchar = nzeros + nsign + s.len() as u32;
    
    let bad_output = nchar > width || (is_neg && !is_dec);
    if bad_output {
        for _ in 0..width {
            buf.write(b"*")?;
        }
    } else {
        let nspace = width - nchar;
        for _ in 0..nspace {
            buf.write(b" ")?;
        }
        if is_neg {
            buf.write(b"-")?;
        }
        for _ in 0..nzeros {
            buf.write(b"0")?;
        }
        buf.write(&s)?;
    }
    
    Ok(())
}

pub(crate) fn serialize_real_f<W: Write>(mut buf: W, v: f64, width: u32, precision: u32, scale: i32) -> SResult<()> {
    let v_is_neg = v < 0.0;
    let v = d2d(v);
    let mut b = itoa::Buffer::new();
    let s = b.format(v.mantissa);
    let m_bytes = s.as_bytes();
    let exponent = v.exponent;

    // For all numbers, we need the decimal place and the numbers after it. For negative numbers,
    // we also need the negative sign.
    let width = width as usize;
    let n_reserved = if v_is_neg { 2 + precision } else { 1 + precision } as usize;

    // Now we need to figure out how many digits to include before the decimal. Some examples:
    // Value    | Mantissa | n_bytes | Exponent | # leading digits |
    // 3.14     | 314      | 3       | -2       | 1                |
    // 0.0314   | 314      | 3       | -4       | 0                |
    // 3140.0   | 314      | 3       | +1       | 4                |
    // 3141.59  | 314159   | 6       | -2       | 4                |
    // So the number of leading digits is max(n_bytes + exponent, 0). Note that for the second example,
    // the leading 0 will be handled specially.
    // Then there's the leading zeros *after* the decimal point. These are only needed if the neg. of the
    // exponent is greater than the number of bytes, in which case the difference is the number of zeros needed.
    // We also need to consider the scale: a positive scale moves the decimal right, so it adds leading
    // digits, and a negative one does the opposite.

    // Now we have enough information to tell if the value is too wide.
    let exp_plus_scale = (exponent + scale) as isize;
    let n_leading_digits = m_bytes.len()
        .saturating_add_signed(exp_plus_scale);
    if n_leading_digits + n_reserved > width {
        for _ in 0..width {
            buf.write(b"*")?;
        }
        return Ok(())
    }

    let wants_leading_zero = n_leading_digits == 0;
    let (n_spaces, print_leading_zero) = if !wants_leading_zero {
        (width - n_reserved - n_leading_digits, false)
    } else if n_leading_digits + n_reserved < width {
        (width - n_reserved - n_leading_digits - 1, true)
    } else {
        (0, false)
    };


    let zeros_after_decimal = if exp_plus_scale >= 0 {
        0
    } else {
        let nexp = (-exp_plus_scale) as usize;
        nexp.saturating_sub(m_bytes.len())
    };

    for _ in 0..n_spaces {
        buf.write(b" ")?;
    }

    if v_is_neg {
        buf.write(b"-")?;
    }

    if print_leading_zero {
        buf.write(b"0")?;
    }

    for i in 0..(n_leading_digits + precision as usize - zeros_after_decimal) {
        if i == n_leading_digits {
            buf.write(b".")?;
            for _ in 0..zeros_after_decimal {
                buf.write(b"0")?;
            }
        }
        let i = i as usize;
        let c = m_bytes.get(i..i+1).unwrap_or(b"0");
        buf.write(c)?;
    }
    Ok(())
}


pub(crate) fn serialize_real_exp<W: Write>(mut buf: W, v: f64, width: u32, precision: u32, scale: i32, exp_ch: &str, n_exp_digits: Option<u32>) -> SResult<()> {
    let v_is_neg = v < 0.0;
    let v = d2d(v);
    
    // This is complicated so some examples using e12.3 as the format
    // Value    | Mantissa | Exponent | Fortran   | Representation 
    // 3.14     | 314      | -2       | 0.314E+01 | (mantissa // 10^3).(mantissa % 10^3)E(exponent+3) 
    // 0.0314   | 314      | -4       | 0.314E-01 | (mantissa // 10^3).(mantissa % 10^3)E(exponent+3)
    // 3140.0   | 314      | +1       | 0.314E+04 | (mantissa // 10^3).(mantissa % 10^3)E(exponent+3)
    // 3141.59  | 314159   | -2       | 0.314E+04 | (mantissa // 10^6).(mantissa % 10^6)E(exponent+6)
    //
    // Then scaling shifts where the decimal point is: +ve moves it right, -ve left. So 3.14 formatted
    // as 1pe12.3 would look like 3.140E+00, and 2pe12.3 like 31.40E-01. With +ve scales, we end up with
    // more sig figs (e.g. 3.1415 formatted as 1pe12.3 becomes 3.141E+00). With -ve scales, we keep the
    // same number of digits after the decimal (so -2pe12.3 => 0.003E+03).
    //
    // Also as far as I can tell for spacing, a leading zero before the decimal is optional, but a negative
    // sign is not. so .314E+01 will fit in an 8-wide format, but not a 7-wide. (At 9-wide it gets the leading 0.)
    // If it's negative (-.314E+01), it needs at least 9 characters. At 10, it becomes -0.314E+01.
    let mantissa = v.mantissa;
    let mut b = itoa::Buffer::new();
    let s = b.format(mantissa);
    let m_bytes = s.as_bytes();
    
    
    let exponent = v.exponent + m_bytes.len() as i32 - scale;
    let mut b = itoa::Buffer::new();
    let s = b.format(exponent.abs());
    let e_bytes = s.as_bytes();
    
    // Include precision # digits, plus decimal point, and the exponent. If the number of digits
    // in the exponent isn't given, it will always be 4 characters wide. (If it needs three digits,
    // the 'E' or 'D' is dropped.) Otherwise it seems to be 2 for the E+ or E- and the number of digits.
    // If the exponent won't fit, this is a number we can't format, so print out the *'s and return.
    let exp_nchar = if let Some(n) = n_exp_digits {
        if e_bytes.len() > n as usize {
            for _ in 0..width {
                buf.write(b"*")?;
            }
            return Ok(())
        }
        n + 2
    } else {
        if e_bytes.len() > 3 {
            for _ in 0..width {
                buf.write(b"*")?;
            }
            return Ok(())
        }
        4
    };
    let min_width = if v_is_neg { precision + 2 + exp_nchar } else { precision + 1 + exp_nchar};
    if width < min_width {
        for _ in 0..width {
            buf.write(b"*")?;
        }
        return Ok(());
    }

    let nspaces = if width > min_width { width - min_width - 1 } else { 0 };
    for _ in 0..nspaces {
        buf.write(b" ")?;
    }

    if v_is_neg {
        buf.write(b"-")?;
    }

    if scale > 0 {
        let mut i = 0;
        for _ in 0..scale {
            let c = m_bytes.get(i..i+1).unwrap_or(b"0");
            buf.write(c)?;
            i += 1;
        }
        buf.write(b".")?;
        let n_after_decimal = if scale <= 1 { precision } else { precision - scale as u32 + 1};
        for _ in 0..n_after_decimal {
            let c = m_bytes.get(i..i+1).unwrap_or(b"0");
            buf.write(c)?;
            i += 1;
        }
    } else {
        if width > min_width {
            // if we have at least one extra character, write the leading zero
            buf.write(b"0")?;
        }
        buf.write(b".")?;
        let mut i = 0;
        for _ in 0..precision {
            if i < -scale {
                buf.write(b"0")?;
            } else {
                let j = (i + scale) as usize;
                let c = m_bytes.get(j..j+1).unwrap_or(b"0");
                buf.write(c)?;
            }
            i += 1;
        }
    }

    let n_digits = if e_bytes.len() < (exp_nchar as usize) - 2 {
        buf.write(exp_ch.as_bytes())?;
        exp_nchar - 2
    } else {
        exp_nchar - 1
    };

    if exponent < 0 {
        buf.write(b"-")?;
    } else {
        buf.write(b"+")?;
    }

    // Pad with 0s if needed
    for _ in 0..(n_digits as usize - e_bytes.len()) {
        buf.write(b"0")?;
    }
    buf.write(e_bytes)?;


    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[derive(Debug, serde::Serialize)]
    struct Test {
        a: &'static str,
        b: i32,
        c: f64
    }

    #[derive(Debug, serde::Serialize)]
    struct HasFlat {
        name: &'static str,
        #[serde(flatten)]
        data: HashMap<String, i32>
    }

    #[derive(Debug, serde::Serialize)]
    struct Nested {
        db_id: i64,
        inner: Test
    }

    #[test]
    fn test_ser_bool() {
        let fmt = FortFormat::parse("(l1)").unwrap();
        let s = to_string(true, &fmt).unwrap();
        assert_eq!(s, "T");
        let s = to_string(false, &fmt).unwrap();
        assert_eq!(s, "F");

        let fmt = FortFormat::parse("(l3)").unwrap();
        let s = to_string(true, &fmt).unwrap();
        assert_eq!(s, "  T");
        let s = to_string(false, &fmt).unwrap();
        assert_eq!(s, "  F");
    }

    #[test]
    fn test_ser_dec_int() {
        let fmt = FortFormat::parse("(i4)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "  42");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, " -42");
        let s = to_string(12345, &fmt).unwrap();
        assert_eq!(s, "****");

        let fmt = FortFormat::parse("(i4.3)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, " 042");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "-042");
        let s = to_string(123, &fmt).unwrap();
        assert_eq!(s, " 123");
        let s = to_string(-123, &fmt).unwrap();
        assert_eq!(s, "-123");

        let fmt = FortFormat::parse("(i3.3)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "042");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "***");
    }

    #[test]
    fn test_octal_int() {
        let fmt = FortFormat::parse("(o5)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "   52");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "*****");

        let fmt = FortFormat::parse("(o5.3)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "  052");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "*****");
    }

    #[test]
    fn test_hex_int() {
        let fmt = FortFormat::parse("(z5)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "   2A");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "*****");

        let fmt = FortFormat::parse("(z5.3)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "  02A");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "*****");
    }

    #[test]
    fn test_char() {
        let fmt = FortFormat::parse("(a)").unwrap();
        let s = to_string('x', &fmt).unwrap();
        assert_eq!(s, "x");

        let fmt = FortFormat::parse("(a2)").unwrap();
        let s = to_string('x', &fmt).unwrap();
        assert_eq!(s, " x");
    }

    #[test]
    fn test_str() {
        let fmt = FortFormat::parse("(a)").unwrap();
        let s = to_string("abcde", &fmt).unwrap();
        assert_eq!(s, "abcde");

        let fmt = FortFormat::parse("(a5)").unwrap();
        let s = to_string("abc", &fmt).unwrap();
        assert_eq!(s, "  abc");
        let s = to_string("abcde", &fmt).unwrap();
        assert_eq!(s, "abcde");
        let s = to_string("abcdefg", &fmt).unwrap();
        assert_eq!(s, "abcde");
    }

    #[test]
    fn test_real_f() {
        let fmt = FortFormat::parse("(f5.3)").unwrap();
        let s = to_string(-0.01, &fmt).unwrap();
        assert_eq!(s, "-.010");

        let fmt = FortFormat::parse("(f4.3)").unwrap();
        let s = to_string(0.314, &fmt).unwrap();
        assert_eq!(s, ".314");

        let fmt = FortFormat::parse("(f8.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   3.140");

        let fmt = FortFormat::parse("(2pf8.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, " 314.000");

        let fmt = FortFormat::parse("(-2pf8.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.031");

        let fmt = FortFormat::parse("(2pf5.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "*****");
    }

    #[test]
    fn test_real_e() {
        let fmt = FortFormat::parse("(e12.3)").unwrap();
        let s = to_string(0.0314, &fmt).unwrap();
        assert_eq!(s, "   0.314E-01");
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.314E+01");
        let s = to_string(3140.0, &fmt).unwrap();
        assert_eq!(s, "   0.314E+04");
        let s = to_string(3141.59, &fmt).unwrap();
        assert_eq!(s, "   0.314E+04");
        let s = to_string(3.14e120, &fmt).unwrap();
        assert_eq!(s, "   0.314+121");

        let fmt = FortFormat::parse("(1pe12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   3.140E+00");
        let s = to_string(3.1415, &fmt).unwrap();
        assert_eq!(s, "   3.141E+00");

        let fmt = FortFormat::parse("(2pe12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   31.40E-01");

        let fmt = FortFormat::parse("(-1pe12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.031E+02");

        let fmt = FortFormat::parse("(-2pe12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.003E+03");

        let fmt = FortFormat::parse("(e7.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "*******");
        let s = to_string(-3.14, &fmt).unwrap();
        assert_eq!(s, "*******");

        let fmt = FortFormat::parse("(e8.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, ".314E+01");
        let s = to_string(-3.14, &fmt).unwrap();
        assert_eq!(s, "********");

        let fmt = FortFormat::parse("(e9.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "0.314E+01");
        let s = to_string(-3.14, &fmt).unwrap();
        assert_eq!(s, "-.314E+01");
        // Don't have these implemented yet - format parsing needs to handle the eN at the end
        // let fmt = FortFormat::parse("(e12.3e1)").unwrap();
        // let s = to_string(3.14e5, &fmt).unwrap();
        // assert_eq!(s, "    0.314E+6");
        // let s = to_string(3.14e15, &fmt).unwrap();
        // assert_eq!(s, "************");

        // let fmt = FortFormat::parse("(e12.3e5)").unwrap();
        // let s = to_string(3.14, &fmt).unwrap();
        // assert_eq!(s, "0.314E+00001");

    }

    #[test]
    fn test_real_d() {
        let fmt = FortFormat::parse("(d12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.314D+01");
        let s = to_string(3.14e120, &fmt).unwrap();
        assert_eq!(s, "   0.314+121");

        let fmt = FortFormat::parse("(1pd12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   3.140D+00");

        let fmt = FortFormat::parse("(-1pd12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.031D+02");

        let fmt = FortFormat::parse("(-2pd12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.003D+03");

    }

    #[test]
    fn test_vec() {
        let fmt = FortFormat::parse("(i3.3,1x,i4.4,1x,i5.5)").unwrap();
        let s = to_string(vec![10,200,3000], &fmt).unwrap();
        assert_eq!(s, "010 0200 03000");
    }

    #[test]
    fn test_tuple() {
        let fmt = FortFormat::parse("(a3,1x,i3.3)").unwrap();
        let s = to_string(("Hi!", 42), &fmt).unwrap();
        assert_eq!(s, "Hi! 042");
    }

    #[test]
    fn test_struct_by_order() {
        let fmt = FortFormat::parse("(a6,1x,i3,1x,e8.3)").unwrap();
        let value = Test { a: "Hello", b: 42, c: 3.14 };
        let s = to_string(value, &fmt).unwrap();
        assert_eq!(s, " Hello  42 .314E+01");
    }

    #[test]
    fn test_struct_by_name() {
        let fmt = FortFormat::parse("(i3,1x,e8.3,1x,a6)").unwrap();
        let value = Test { a: "Hello", b: 42, c: 3.14 };
        let s = to_string_with_fields(value, &fmt, &["b", "c", "a"]).unwrap();
        assert_eq!(s, " 42 .314E+01  Hello");
    }

    #[test]
    fn test_map_by_name() {
        let value = HashMap::from([
            ("a", 2),
            ("b", 4),
            ("c", 8)
        ]);
        let fmt = FortFormat::parse("(3i2)").unwrap();
        let s= to_string_with_fields(value, &fmt, &["b", "a", "c"]).unwrap();
        assert_eq!(s, " 4 2 8");
    }

    #[test]
    fn test_struct_with_flattened_map() {
        let data = HashMap::from([
            ("co2".to_string(), 400_000),
            ("ch4".to_string(), 1900),
            ("n2o".to_string(), 310),
            ("co".to_string(), 100)
        ]);
        let value = HasFlat { name: "pa", data };
        let fmt = FortFormat::parse("(a2,4(1x,i6))").unwrap();
        let s = to_string_with_fields(value, &fmt, &["name", "n2o", "co", "co2", "ch4"]).unwrap();
        assert_eq!(s, "pa    310    100 400000   1900");
    }

    #[test]
    fn test_nested_struct_by_order() {
        let inner = Test { a: "Hello", b: 42, c: 3.14 };
        let value = Nested { db_id: 1, inner };
        let fmt = FortFormat::parse("(i2,1x,a5,1x,i2,1x,e8.3)").unwrap();
        let s = to_string(value, &fmt).unwrap();
        assert_eq!(s, " 1 Hello 42 .314E+01");
    }

    #[test]
    fn test_nested_struct_by_name() {
        let inner = Test { a: "Hello", b: 42, c: 3.14 };
        let value = Nested { db_id: 1, inner };
        let fmt = FortFormat::parse("(e8.3,1x,i2,1x,a5,1x,i1)").unwrap();
        // this gives a "missing field 'inner' error", which is what we expected for now.
        let e = to_string_with_fields(value, &fmt, &["c", "b", "a", "db_id"]);
        assert!(e.is_err());
    }

    #[test]
    fn test_external_enums() {
        #[derive(Debug, serde::Serialize)]
        enum External {
            Alpha(i32),
            Beta(i32),
        }

        let ex_vec = vec![External::Alpha(12), External::Beta(24)];
        let ex_ff = FortFormat::parse("(2(a6,i3))").unwrap();
        let ex_s = to_string(&ex_vec, &ex_ff).unwrap();
        assert_eq!(ex_s, " Alpha 12  Beta 24");        
    }

    #[test]
    fn test_internal_enums() {
        #[derive(Debug, serde::Serialize)]
        #[serde(tag = "type")]
        enum Internal {
            Alpha{value: i32},
            Beta{value: i32},
        }

        let in_vec = vec![Internal::Alpha{value: 12}, Internal::Beta{value: 24}];
        let in_ff = FortFormat::parse("(2(a6,i3))").unwrap();
        let in_s = to_string(&in_vec, &in_ff).unwrap();
        assert_eq!(in_s, " Alpha 12  Beta 24");

        let fields = ["type", "value"];
        let ff = FortFormat::parse("(a5,1x,i2)").unwrap();
        let s = to_string_with_fields(
            Internal::Alpha { value: 42 },
            &ff,
            &fields
        ).unwrap();
        // TODO: ideally we want the tag field to be sorted according to the field names
        // - need to better understand how different enum representations are handled.
        assert_ne!(s, "42 Alpha");
    }

    #[test]
    fn test_adjacent_enums() {
        #[derive(Debug, serde::Serialize)]
        #[serde(tag = "key", content = "value")]
        enum Adjacent {
            Alpha(i32),
            Beta(i32),
        }

        let adj_vec = vec![Adjacent::Alpha(12), Adjacent::Beta(24)];
        let adj_ff = FortFormat::parse("(2(a6,i3))").unwrap();
        let adj_s = to_string(&adj_vec, &adj_ff).unwrap();
        assert_eq!(adj_s, " Alpha 12  Beta 24");
    }

    #[test]
    fn test_untagged_enums() {
        #[derive(Debug, serde::Serialize)]
        #[serde(untagged)]
        enum Untagged {
            Alpha(i32),
            Beta(f32),
        }

        let un_vec = vec![Untagged::Alpha(12), Untagged::Beta(24.0)];
        let un_ff = FortFormat::parse("(i3,f6.1)").unwrap();
        let un_s = to_string(&un_vec, &un_ff).unwrap();
        assert_eq!(un_s, " 12  24.0");
    }

    #[test]
    fn test_enum_into() {
        #[derive(Debug, Clone, serde::Serialize)]
        #[serde(into = "String")]
        enum InstrumentValue {
            Nothing,
            Value(f32),
            ValueWithError(f32, f32)
        }
        
        impl From<InstrumentValue> for String {
            fn from(value: InstrumentValue) -> Self {
                match value {
                    InstrumentValue::Nothing => "Nothing".to_string(),
                    InstrumentValue::Value(v) => format!("{v:.3}"),
                    InstrumentValue::ValueWithError(v, e) => format!("{v:.1}+/-{e:.1}"),
                }
            }
        }

        let values = [
            InstrumentValue::Nothing,
            InstrumentValue::Value(1.0),
            InstrumentValue::ValueWithError(2.0, 0.2)
        ];
        let ff = FortFormat::parse("(3a12)").unwrap();
        let s = to_string(values, &ff).unwrap();
        assert_eq!(s, "     Nothing       1.000   2.0+/-0.2");
    }

    #[test]
    fn test_none_default_fill() {
        let fmt = FortFormat::parse("(a,1x,a3,1x,l1,1x,i5,1x,f8.3)").unwrap();
        let value: (Option<String>, Option<String>, Option<bool>, Option<i32>, Option<f32>) = (None, None, None, None, None);
        let s = to_string(value, &fmt).unwrap();
        assert_eq!(s, "* *** * ***** ********");
    }

    #[test]
    fn test_none_string_fill() {
        let settings = SerSettings { 
            fill_method: NoneFill::String("FILL_VAL".as_bytes().to_vec())
        };
        let fmt = FortFormat::parse("(a,1x,a3,1x,l1,1x,i5,1x,f8.3)").unwrap();
        let value: (Option<String>, Option<String>, Option<bool>, Option<i32>, Option<f32>) = (None, None, None, None, None);
        let s = to_string_custom(value, &fmt, None, settings).unwrap();
        assert_eq!(s, "F FIL F FILL_ FILL_VAL");
    }

    #[test]
    fn test_none_partial_typed_fill() {
        let settings = SerSettings { 
            fill_method: NoneFill::new_partial_typed(-999, -999.999)
        };
        let fmt = FortFormat::parse("(a,1x,a3,1x,l1,1x,i5,1x,f8.3)").unwrap();
        let value: (Option<String>, Option<String>, Option<bool>, Option<i32>, Option<f32>) = (None, None, None, None, None);
        let s = to_string_custom(value, &fmt, None, settings).unwrap();
        assert_eq!(s, "* *** *  -999 -999.999");
    }

    #[test]
    fn test_none_typed_fill() {
        let settings = SerSettings { 
            fill_method: NoneFill::new_typed(false, -999, -999.999, "N/A")
        };
        let fmt = FortFormat::parse("(a,1x,a3,1x,l1,1x,i5,1x,f8.3)").unwrap();
        let value: (Option<String>, Option<String>, Option<bool>, Option<i32>, Option<f32>) = (None, None, None, None, None);
        let s = to_string_custom(value, &fmt, None, settings).unwrap();
        assert_eq!(s, "N/A N/A F  -999 -999.999");
    }

    #[test]
    fn test_unit_type_fills() {
        // Since unit types are treated the same as `None` (at least as of 19 Feb 2024)
        // we rely on the none tests to ensure that alternate fill settings work.
        #[derive(serde::Serialize)]
        struct Empty;
        let fmt = FortFormat::parse("(i5,1x,f8.3)").unwrap();
        let value = ((), Empty);
        let s = to_string(value, &fmt).unwrap();
        assert_eq!(s, "***** ********");
    }
}