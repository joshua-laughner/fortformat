//! Deserialize data written according to a Fortran format string
//! 
//! # Basic usage
//! 
//! This module expects that you have a Fortran format string, such as
//! `(a10,i3,f8.2)` and want to deserialize data that was written out
//! according to that format. The functions provided by this module
//! belong to two groups: `from_*` and `from_*_with_fields`. The distinction
//! mainly matters when deserializing into structures. The `from_*` functions
//! will output values in the order they are defined. That is, this example
//! will work, because the fields in `Person` are defined in the same order
//! as they appear in the data:
//! 
//! ```
//! use fortformat::format_specs::FortFormat;
//! use fortformat::de::from_str;
//! 
//! #[derive(Debug, PartialEq, serde::Deserialize)]
//! struct Person {
//!     name: String,
//!     age: i32,
//!     weight: f32,
//! }
//! 
//! let ff = FortFormat::parse("(a10,i3,f8.1)").unwrap();
//! let p: Person = from_str("John Doe   30   180.5", &ff).unwrap();
//! assert_eq!(p, Person{name: "John Doe".to_string(), age: 30, weight: 180.5});
//! ```
//! 
//! However, the next example will *not* work, because the field order does not match
//! the data:
//! 
//! ```
//! use fortformat::serde_common::DResult;
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::de::from_str;
//! # 
//! # #[derive(Debug, PartialEq, serde::Deserialize)]
//! # struct Person {
//! #     name: String,
//! #     age: i32,
//! #     weight: f32,
//! # }
//! let ff = FortFormat::parse("(f8.1,i3,1x,a10)").unwrap();
//! let res: DResult<Person> = from_str("   180.5 30 John Doe  ", &ff);
//! assert!(res.is_err())
//! ```
//! 
//! If you need to handle fields in arbitrary order, use [`from_str_with_fields`] instead.
//! You will need to parse the input enough to get the field names and order. Once you
//! have that, you can do:
//! 
//! ```
//! # use fortformat::serde_common::SResult;
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::de::from_str_with_fields;
//! # 
//! # #[derive(Debug, PartialEq, serde::Deserialize)]
//! # struct Person {
//! #     name: String,
//! #     age: i32,
//! #     weight: f32,
//! # }
//! let ff = FortFormat::parse("(f8.1,i3,1x,a10)").unwrap();
//! let fieldnames = ["weight", "age", "name"];
//! let p: Person = from_str_with_fields("   180.5 30 John Doe  ", &ff, &fieldnames).unwrap();
//! assert_eq!(p, Person{name: "John Doe".to_string(), age: 30, weight: 180.5});
//! ```
//! 
//! # Deserializing optional values
//! 
//! Fortran does not have the concept of a null value. When reading in data, if the input
//! ends before all the input variables have been populated, they will either have their previous
//! value or the program will crash:
//! 
//! ```fortran
//! program reading
//! 
//! implicit none
//! 
//! integer*4 x, y, z
//! character*16 s
//! 
//! x = -99
//! y = -99
//! z = -99
//! 
//! ! A slash indicates the end of input to parse
//! s = '1 2 / 3'
//! read(s, *) x, y, z
//! write(*,*) 'z = ', z  ! z will still be -99
//! 
//! s = '4 5'
//! read(s, *), x, y, z
//! ! crashes with "End of file" error
//! 
//! end program
//! ```
//! 
//! For this crate, we treat both cases more consistently: if `z` is an `Option`,
//! then in both cases it will be a `None`. If it is not an `Option`, then parsing
//! either string will result in an error:
//! 
//! ```
//! use fortformat::format_specs::FortFormat;
//! use fortformat::de::from_str;
//! use fortformat::serde_common::DError;
//! 
//! let ff = FortFormat::ListDirected;
//! let (x, y, z): (i32, i32, Option<i32>) = from_str("1 2 / 3", &ff).unwrap();
//! assert_eq!(x, 1);
//! assert_eq!(y, 2);
//! assert_eq!(z, None);
//! 
//! let (x, y, z): (i32, i32, Option<i32>) = from_str("4 5", &ff).unwrap();
//! assert_eq!(x, 4);
//! assert_eq!(y, 5);
//! assert_eq!(z, None);
//! 
//! let res: Result<(i32, i32, i32), _> = from_str("7 8", &ff);
//! assert!(res.is_err())
//! ```
//! 
//! # Deserializing nested structures
//! 
//! ## Known data order
//! 
//! Data formatted by Fortran tends to be flat (without nesting) unlike e.g. JSON. However,
//! we can translate such data into nested data structures. If you can rely on the order
//! of the fields to match the data (such that you can use [`from_str`]), then nested structures
//! will deserialize as you expect:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::de::from_str;
//! 
//! #[derive(Debug, PartialEq, serde::Deserialize)]
//! struct Location {
//!     name: String,
//!     coords: Coordinates
//! }
//! 
//! #[derive(Debug, PartialEq, serde::Deserialize)]
//! struct Coordinates {
//!     x: i32,
//!     y: i32
//! }
//! 
//! let ff = FortFormat::parse("(a5,1x,i3,1x,i3)").unwrap();
//! let loc: Location = from_str("First 123 456", &ff).unwrap();
//! assert_eq!(loc, Location{ name: "First".to_string(), coords: Coordinates{ x: 123, y: 456 }})
//! ```
//! 
//! This works because the deserializer knows that no Fortran format specifier represents a structure.
//! In this case its process it:
//! 
//! 1. Try to deserialize the "a5" string into the `name` field. The types match so this works and it advances
//!    to the next format specifier.
//! 2. Inspect the next field. It is a struct, so descend into it and do not try to parse the next specified value ("i3").
//! 3. Inside `coords`, it finds an integer. This is a type it can deserialize, so it parses the next part of
//!    the string according to the "i3" format, since that type matches the `x` field.
//! 4. Repeat for the `y` field.
//! 
//! Essentially, the deserializer will only try to consume a format specifier when visiting a non-compound field 
//! on a structure.
//! 
//! ## Unknown data order
//! 
//! If you want to deserialize into a nested structure and you do not know (or cannot trust) the order of the
//! fields in the data, then you will need to use serde's `flatten` attribute as in the following:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! # use fortformat::de::from_str_with_fields;
//! 
//! #[derive(Debug, PartialEq, serde::Deserialize)]
//! struct Location {
//!     name: String,
//!     #[serde(flatten)]
//!     coords: Coordinates
//! }
//! 
//! #[derive(Debug, PartialEq, serde::Deserialize)]
//! struct Coordinates {
//!     x: i32,
//!     y: i32
//! }
//! 
//! let ff = FortFormat::parse("(i3,1x,i3,1x,a5)").unwrap();
//! let loc: Location = from_str_with_fields("123 456 First", &ff, &["x", "y", "name"]).unwrap();
//! assert_eq!(loc, Location{ name: "First".to_string(), coords: Coordinates{ x: 123, y: 456 }})
//! ```
//! 
//! Without `#[serde(flatten)]` on the `Location.coords` field, the deserializer would expect there to
//! be a field name "coords" in the list. In this case, `flatten` is needed to hint to it ahead of time
//! that `coords` isn't a field in the data, but its own fields are.
//! 
//! # Adjusting deserialization settings
//! 
//! Fortran has some other quirks that we want to ignore most of the time. For example, strings in Fortran
//! are fixed-length arrays, usually padded with spaces if the actual string is shorter than the array.
//! Normally, we trim whitespace from Fortran strings so that the returned value is sensible for Rust.
//! However, if that leading or trailing whitespace matters, you can disable this behavior by using
//! [`from_str_custom`] or [`from_str_with_fields_custom`] and passing an instance of [`DeSettings`]:
//! 
//! ```
//! use fortformat::format_specs::FortFormat;
//! use fortformat::de::{from_str, from_str_custom, DeSettings};
//! 
//! let ff = FortFormat::parse("(a10)").unwrap();
//! let s: String = from_str("Hello     ", &ff).unwrap();
//! assert_eq!(s, "Hello");  // trailing whitespace has been trimmed
//! 
//! let settings = DeSettings::default()
//!     .do_trim(false);
//! let s: String = from_str_custom("Hello     ", &ff, settings).unwrap();
//! assert_eq!(s, "Hello     ");
//! ```
//! 
//! Our convention is that deserializing functions that accept settings will end in `_custom`,
//! and the non-custom version of those functions uses `DeSettings::default()`.

use serde::de::{self, SeqAccess, MapAccess, Visitor};
use crate::fort_error::FError;
use crate::serde_common::{DResult, DError};
use crate::format_specs::FortField;
pub use crate::format_specs::{FortValue, FortFormat};
use crate::parsing;

/// Settings for deserializing Fortran data
/// 
/// To use, instantiate the default version with `DeSettings::default()` and
/// modify the desired settings with the public methods:
/// 
/// ```
/// # use fortformat::de::DeSettings;
/// 
/// let settings = DeSettings::default().do_trim(false);
/// ```
#[derive(Debug, Clone)]
pub struct DeSettings {
    trim_strings: bool,
}

impl DeSettings {
    /// Set whether to trim leading and trailing whitespace from deserialized strings.
    /// 
    /// Default is `true`, i.e. do remove the whitespace.
    pub fn do_trim(mut self, trim_strings: bool) -> Self {
        self.trim_strings = trim_strings;
        self
    }
}

impl Default for DeSettings {
    fn default() -> Self {
        Self { trim_strings: true }
    }
}


/// Deserialize data from a string in memory.
/// 
/// For structures, the fields will be deserialized in order
/// (assuming `Deserialize` is derived). To use field names,
/// see [`from_str_with_fields`].
pub fn from_str<'a, T>(s: &'a str, fmt: &'a FortFormat) -> DResult<T> 
where T: de::Deserialize<'a>
{
    from_str_custom(s, fmt, DeSettings::default())
}

/// Deserialize data from a string in memory with customized settings.
/// 
/// For structures, the fields will be deserialized in order
/// (assuming `Deserialize` is derived). To use field names,
/// see [`from_str_with_fields_custom`].
pub fn from_str_custom<'a, T>(s: &'a str, fmt: &'a FortFormat, settings: DeSettings) -> DResult<T> 
where T: de::Deserialize<'a>
{
    let mut deserializer: Deserializer<'_, &str> = Deserializer::from_str(s, fmt, settings);
    let t = T::deserialize(&mut deserializer)?;
    Ok(t)
}

/// Deserialize data from a string in memory with field names given.
/// 
/// For structures, the field names given as `fields` will be used to match values
/// with the correct fields in the structure, rather than relying on order. If field names
/// are not available (and you must rely on the order in the data), see [`from_str`].
pub fn from_str_with_fields<'a, T, F>(s: &'a str, fmt: &'a FortFormat, fields: &'a[F]) -> DResult<T> 
where T: de::Deserialize<'a>,
      F: AsRef<str>
{
    from_str_with_fields_custom(s, fmt, fields, DeSettings::default())
}

/// Deserialize data from a string in memory with field names given and customized settings.
/// 
/// For structures, the field names given as `fields` will be used to match values
/// with the correct fields in the structure, rather than relying on order. If field names
/// are not available (and you must rely on the order in the data), see [`from_str_custom`].
pub fn from_str_with_fields_custom<'a, T, F>(s: &'a str, fmt: &'a FortFormat, fields: &'a[F], settings: DeSettings) -> DResult<T> 
where T: de::Deserialize<'a>,
      F: AsRef<str>
{
    let mut deserializer = Deserializer::from_str_with_fields(s, fmt, fields, settings);
    let t = T::deserialize(&mut deserializer)?;
    Ok(t)
}

/// Deserializer for Fortran-formatted data.
pub struct Deserializer<'de, F: AsRef<str>> {
    settings: DeSettings,
    input: &'de str,
    input_idx: usize,
    fmt: &'de FortFormat,
    fmt_idx: usize,
    field_idx: usize,
    fields: Option<&'de [F]>,
    found_terminal_char: bool,
}


impl<'de, F: AsRef<str>> Deserializer<'de, F> {
    pub fn from_str(input: &'de str, fmt: &'de FortFormat, settings: DeSettings) -> Self {
        Self { settings, input, input_idx: 0, fmt, fmt_idx: 0, field_idx: 0, fields: None, found_terminal_char: false }
    }

    pub fn from_str_with_fields(input: &'de str, fmt: &'de FortFormat, fields: &'de[F], settings: DeSettings) -> Self {
        Self { settings, input, input_idx: 0, fmt, fmt_idx: 0, field_idx: 0, fields: Some(fields), found_terminal_char: false }
    }

    fn advance_over_skips(&mut self) {
        loop {
            // Consume any skips (i.e. 1x, 2x) in the format, also advancing
            // the internal string. This can be modified to handle other types
            // of Fortran positioning formats in the future.
            let peeked_fmt = self.fmt.get_field(self.fmt_idx);
            match peeked_fmt {
                Some(&FortField::Skip) => {
                    self.fmt_idx += 1;
                    let _ = self.next_n_bytes(1);
                }
                _ => return,
            }
        }
    }

    fn next_fmt(&mut self) -> DResult<&FortField> {
        self.advance_over_skips();
        loop {
            let next_fmt = self.fmt.get_field(self.fmt_idx);
            match next_fmt {
                Some(field) => {
                    self.fmt_idx += 1;
                    self.field_idx += 1;
                    return Ok(field)
                },
                None => return Err(DError::FormatSpecTooShort)
            }
        }
    }

    fn curr_field(&self) -> Option<&str> {
        if let Some(fields) = self.fields {
            fields.get(self.field_idx).map(|f| f.as_ref())
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
            .map(|f| f.as_ref())
    }

    #[allow(dead_code)] // keeping this function for now in case it is needed later
    fn peek_fmt(&mut self) -> Option<&FortField> {
        self.advance_over_skips();
        self.fmt.get_field(self.fmt_idx)
    }

    fn rewind_fmt(&mut self) {
        if self.fmt_idx == 0 {
            return;
        }

        // None of the deserializers consume characters until the format has been matched,
        // so we only need to reset the format and field indices, not the character index.
        self.fmt_idx = self.fmt_idx.saturating_sub(1);
        self.field_idx = self.field_idx.saturating_sub(1);

    }

    fn next_n_bytes(&mut self, n: u32) -> Result<&'de str, DError> {
        let n: usize = n.try_into().expect("Could not fit u32 into usize");
        let mut nbytes = 0;
        for c in self.input[self.input_idx..].chars() {
            nbytes += c.len_utf8();
            if nbytes >= n { break; }
        }

        if nbytes < n {
            return Err(DError::InputEndedEarly)
        }

        let s = &self.input[self.input_idx..self.input_idx+nbytes];
        self.input_idx += nbytes;
        Ok(s)
    }

    fn has_n_bytes_remaining(&self, n: u32) -> bool {
        self.input.len() > n as usize
    }

    #[allow(dead_code)] // keeping this function for now in case it is needed later
    fn prev_n_bytes(&mut self, n: u32) {
        let n: usize = n.try_into().expect("Could not fit u32 into usize");
        let mut nbytes = 0;
        for c in self.input[..self.input_idx].chars().rev() {
            nbytes += c.len_utf8();
            if nbytes >= n { break; }
        }

        self.input_idx -= nbytes;
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.input_idx..].chars().next()
    }

    fn next_list_directed_substring(&mut self, peek: bool) -> Result<&'de str, DError> {
        self.skip_list_separators();

        let next_char = self.peek_char()
            .ok_or_else(|| DError::InputEndedEarly)?;

        if next_char == '\'' || next_char == '"' {
            // take characters until the next quote - it looks like F77 at least does not
            // allow for escaping quotes: https://docs.oracle.com/cd/E19957-01/805-4939/6j4m0vnc5/index.html#c400000b7b12
            self.take_quoted_string(peek)
        } else {
            // take characters until the next space, comma, or slash
            self.take_until_sep(peek)
        }
    }

    fn take_quoted_string(&mut self, peek: bool) -> Result<&'de str, DError> {
        if self.found_terminal_char {
            return Err(DError::InputEndedEarly)
        }

        let mut chars = self.input[self.input_idx..].chars();
        let quote = chars.next().expect("Called take_quoted_string when all characters in the input had already been read.");
        let mut nbytes = quote.len_utf8();
        let mut found_end_quote = false;

        for c in chars {
            nbytes += c.len_utf8();
            if c == quote {
                found_end_quote = true;
                break;
            }
        }

        if !found_end_quote {
            return Err(DError::ClosingQuoteMissing{quote, start_byte: self.input_idx});
        }

        let nbq = quote.len_utf8();
        // Only return the part of the string inside the quotes
        let inner_str = &self.input[self.input_idx+nbq..self.input_idx+nbytes-nbq];
        if !peek {
            self.input_idx += nbytes;
        }
        
        Ok(inner_str)
    }

    fn take_until_sep(&mut self, peek: bool) -> Result<&'de str, DError> {
        if self.found_terminal_char {
            return Err(DError::InputEndedEarly)
        }

        let start = self.input_idx;
        loop {
            let c = self.peek_char();
            if Self::is_list_sep(c) {
                break;
            } else if Self::is_terminal_char(c) {
                self.found_terminal_char = true;
                break; 
            } else {
                self.input_idx += c.map(|c| c.len_utf8()).unwrap_or(0);
            }
        }

        let s = &self.input[start..self.input_idx];
        if peek {
            self.input_idx = start;
        }
        Ok(s)
    }

    fn skip_list_separators(&mut self) {
        loop {
            let c = self.peek_char();
            if Self::is_list_sep(c) {
                self.input_idx += c.map(|c| c.len_utf8()).unwrap_or(0);
                if c.is_none() {
                    self.found_terminal_char = true;
                    break;
                }
            } else if Self::is_terminal_char(c) { 
                self.found_terminal_char = true;
                break;
            } else {
                break;
            }
        }
    }

    fn is_list_sep(c: Option<char>) -> bool {
        if let Some(c) = c {
            c.is_ascii_whitespace() || c == ','
        } else {
            true
        }
    }

    fn is_terminal_char(c: Option<char>) -> bool {
        c.is_some_and(|c| c == '/')
    }


}

impl<'de, 'a, F: AsRef<str>> de::Deserializer<'de> for &'a mut Deserializer<'de, F> {
    type Error = DError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {

        // Note: this was needed to deserialize a struct with an inner flattened struct
        match self.peek_fmt() {
            None => Err(DError::FormatSpecTooShort),
            Some(FortField::Char { width: _ }) => self.deserialize_str(visitor),
            Some(FortField::Integer { width: _, zeros: _, base: _ }) => self.deserialize_i64(visitor),
            Some(FortField::Logical { width: _ }) => self.deserialize_bool(visitor),
            Some(FortField::Real { width: _, precision: _, fmt: _, scale: _ }) => self.deserialize_f64(visitor),
            Some(FortField::Any) => {
                self.next_fmt()?;
                let s = self.next_list_directed_substring(false)?;
                let c1 = s.chars().next().unwrap_or(' ');
                if c1.is_ascii_digit() || c1 == '+' || c1 == '-' {
                    if let Ok(v) = parsing::parse_integer(s) {
                        return visitor.visit_i64(v);
                    }

                    if let Ok(v) = parsing::parse_any_real(s) {
                        return visitor.visit_f64(v);
                    }
                }

                if let Ok(v) = parsing::parse_logical(s) {
                    return visitor.visit_bool(v);
                }

                return visitor.visit_str(s);
            },
            Some(FortField::Skip) => panic!("Got a skip format during peak")
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Logical { width } = next_fmt {
            let substr = self.next_n_bytes(width)?;
            let b = parsing::parse_logical(substr)?;
            visitor.visit_bool(b)
        } else if let FortField::Any = next_fmt {
            let substr = self.next_list_directed_substring(false)?;
            let b = parsing::parse_logical(substr)?;
            visitor.visit_bool(b)
        } else {
            Err(DError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "bool", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_i64(visitor)
        .map_err(|e| e.with_serde_type("i8"))
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
            self.deserialize_i64(visitor)
            .map_err(|e| e.with_serde_type("i16"))
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_i64(visitor)
        .map_err(|e| e.with_serde_type("i32"))
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Integer { width, zeros: _, base } = next_fmt {
            let substr = self.next_n_bytes(width)?;
            let v = match base {
                crate::format_specs::IntBase::Decimal => parsing::parse_integer(substr)?,
                crate::format_specs::IntBase::Octal => todo!(),
                crate::format_specs::IntBase::Hexadecimal => todo!(),
            };
            visitor.visit_i64(v)
        } else if let FortField::Any = next_fmt {
            // I don't think octal and hexadecimal integers are supported in list-directed input.
            let substr = self.next_list_directed_substring(false)?;
            let v = parsing::parse_integer(substr)?;
            visitor.visit_i64(v)
        } else {
            Err(DError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "i64", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
            self.deserialize_u64(visitor)
            .map_err(|e| e.with_serde_type("u8"))
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_u64(visitor)
        .map_err(|e| e.with_serde_type("u16"))
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_u64(visitor)
        .map_err(|e| e.with_serde_type("u32"))
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
            let next_fmt = *self.next_fmt()?;
            if let FortField::Integer { width, zeros: _, base } = next_fmt {
                let substr = self.next_n_bytes(width)?;
                let v = match base {
                    crate::format_specs::IntBase::Decimal => parsing::parse_unsigned_integer(substr)?,
                    crate::format_specs::IntBase::Octal => todo!(),
                    crate::format_specs::IntBase::Hexadecimal => todo!(),
                };
                visitor.visit_u64(v)
            } else if let FortField::Any = next_fmt {
                // I don't think octal and hexadecimal integers are supported in list-directed input.
                let substr = self.next_list_directed_substring(false)?;
                let v = parsing::parse_unsigned_integer(substr)?;
                visitor.visit_u64(v)
            } else {
                Err(DError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "u64", field_name: self.try_prev_field().map(|f| f.to_string()) })
            }
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_f64(visitor)
        .map_err(|e| e.with_serde_type("f32"))
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Real { width, precision: _, fmt, scale } = next_fmt {
            // First handle initial parsing
            let substr = self.next_n_bytes(width)?;
            let substr = substr.trim(); // Fortran format allows padding with spaces, but Rust does not
            let res = if fmt.is_d() {
                let valstr = substr.replace("d", "e").replace("D", "E");
                valstr.parse::<f64>()
            } else {
                substr.parse::<f64>()
            };
            let v = res.map_err(|e| FError::ParsingError { s: substr.to_string(), t: "real", reason: format!("Invalid real number format ({e})") })?;

            // Handle the edge case of an F format with a scale factor - on output with Np
            // the value is multiplied by 10^N so on input we need to multiply by 10^-N.
            let v = if fmt.is_f() && scale != 0 {
                v * 10.0_f64.powi(-scale)
            } else {
                v
            };
            visitor.visit_f64(v)
        } else if let FortField::Any = next_fmt {
            // Fortran format allows padding with spaces, but Rust does not, hence the trim()
            let substr = self.next_list_directed_substring(false)?.trim();
            let v = parsing::parse_any_real(substr)?;
            
            // Unlike with fixed format, there's no edge case of values being multiplied
            // by a power of 10.
            visitor.visit_f64(v)
        } else {
            Err(DError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "f64", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        match next_fmt {
            FortField::Char { width: None } | FortField::Char { width: Some(1) } => {
                let c = self.next_n_bytes(1)?
                    .chars()
                    .next()
                    .unwrap();  // Ok to unwrap, next_n_chars returns an error if not enough characters available.
                visitor.visit_char(c)
            },
            FortField::Char { width: _ } => {
                Err(DError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "char (requires 'a' or 'a1' Fortran format)", field_name: self.try_prev_field().map(|f| f.to_string()) })
            },
            FortField::Any => {
                let s: Vec<char> = self.next_list_directed_substring(false)?
                    .chars()
                    .collect();
                if s.len() != 1 {
                    Err(DError::FormatTypeMismatch { 
                        spec_type: next_fmt, 
                        serde_type: "char (list-directed parsing provided a substring with 0 or >1 characters)", 
                        field_name: self.try_prev_field().map(|f| f.to_string()) 
                    })
                } else {
                    visitor.visit_char(s[0])
                }
            }
            _ => {
                Err(DError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "char", field_name: self.try_prev_field().map(|f| f.to_string()) })
            }
        }
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Char { width } = next_fmt {
            let s = self.next_n_bytes(width.unwrap_or(1))?;
            if self.settings.trim_strings {
                visitor.visit_borrowed_str(s.trim())
            } else {
                visitor.visit_borrowed_str(s)
            }
        } else if let FortField::Any = next_fmt {
            let s = self.next_list_directed_substring(false)?;
            if self.settings.trim_strings {
                visitor.visit_borrowed_str(s.trim())
            } else {
                visitor.visit_borrowed_str(s)
            }
        } else {
            Err(DError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "&str", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
        
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_str(visitor)
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        // Fortran doesn't really have a mechanism to indicate a null value,
        // so it really only makes sense to return a none if we're out of format
        // elements or input.
        self.advance_over_skips();
        let next_fmt = self.peek_fmt().map(|f| *f);

        let visit_some = match next_fmt {
            Some(FortField::Any) => {
                self.skip_list_separators();
                !self.found_terminal_char && self.has_n_bytes_remaining(1)
            },
            Some(FortField::Char { width }) => self.has_n_bytes_remaining(width.unwrap_or(1)),
            Some(FortField::Integer { width, zeros: _, base: _ }) => self.has_n_bytes_remaining(width),
            Some(FortField::Logical { width }) => self.has_n_bytes_remaining(width),
            Some(FortField::Real { width, precision: _, fmt: _, scale: _ }) => self.has_n_bytes_remaining(width),
            Some(FortField::Skip) => panic!("Any skip format specifiers should have been skipped over"),
            None => false,
        };

        if visit_some {
            visitor.visit_some(self)
        } else {
            visitor.visit_none()
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_unit_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_newtype_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        visitor.visit_seq(UnknownLenSeq::new(self, None))
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        visitor.visit_seq(KnownLenSeq::new(self, len))
    }

    fn deserialize_tuple_struct<V>(
        self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        
        if self.fields.is_some() {
            // Note: this was needed when deserializing a struct with a flattened inner struct
            let map_accessor = FieldSequence::new(self);
            visitor.visit_map(map_accessor)
        } else {
            todo!()
        }
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        
        if self.fields.is_some() {
            let map_accessor = FieldSequence::new(self);
            visitor.visit_map(map_accessor)
        } else {
            // We'll assume that structures should read their fields in order from the input
            // and so deserialize them as known length sequences.
            visitor.visit_seq(KnownLenSeq::new(self, fields.len()))
        }
    }

    fn deserialize_enum<V>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        
        // If this deserializer was provided with field names from e.g. a table header,
        // try to use those. Otherwise, assume that an identifer is given as the next
        // string in the format.
        if let Some(fields) = self.fields {
            let this_field = fields.get(self.field_idx)
                .map(|f| f)
                .ok_or_else(|| DError::FieldListTooShort)?;
            visitor.visit_borrowed_str(this_field.as_ref())
        } else {
            // Note: as of 2023-10-20, this else clause isn't supporting a specific data
            // layout, it is just to handle the no-fields case.
            self.deserialize_str(visitor)
        }
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        // Note: this was called in the non-flattened inner struct test with fields.
        // That suggests there *might* be a way to know whether we should advance the
        // field and format indices.
        self.deserialize_any(visitor)
    }
}


struct KnownLenSeq<'a, 'de: 'a, F: AsRef<str>> {
    de: &'a mut Deserializer<'de, F>,
    n: usize,
    i: usize,
}

impl<'a, 'de, F: AsRef<str>> KnownLenSeq<'a, 'de, F> {
    fn new(de: &'a mut Deserializer<'de, F>, n: usize) -> Self {
        Self { de, n, i: 0 }
    }
}

impl<'de, 'a, F: AsRef<str>> SeqAccess<'de> for KnownLenSeq<'a, 'de, F> {
    type Error = DError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: de::DeserializeSeed<'de> {
        
        if self.i == self.n {
            // Check if we've already deserialized all the elements we are supposed to
            // and stop if so.
            Ok(None)
        } else {
            // Otherwise we can just deserialize whatever the next element is
            self.i += 1;
            seed.deserialize(&mut *self.de).map(Some)
        }
    }
}


struct UnknownLenSeq<'a, 'de: 'a, F: AsRef<str>> {
    de: &'a mut Deserializer<'de, F>,
    n: usize,
    max_n: Option<usize>
}

impl<'a, 'de, F: AsRef<str>> UnknownLenSeq<'a, 'de, F> {
    fn new(de: &'a mut Deserializer<'de, F>, max_n: Option<usize>) -> Self {
        Self { de, n: 0, max_n }
    }
}

impl<'de, 'a, F: AsRef<str>> SeqAccess<'de> for UnknownLenSeq<'a, 'de, F> {
    type Error = DError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: de::DeserializeSeed<'de> {
        
        // First check if we've already deserialized the maximum number of allowed values
        // and stop if so
        if let Some(m) = self.max_n {
            if m == self.n {
                return Ok(None)
            }
        }

        // Otherwise we try to deserialize the next value in the sequence. Some errors tell us
        // to end the sequence, others are actual errors.
        match seed.deserialize(&mut *self.de) {
            Ok(el) => Ok(Some(el)),
            Err(DError::FormatTypeMismatch { spec_type: _, serde_type: _, field_name: _ }) => {
                self.de.rewind_fmt();
                Ok(None)
            }, // different type than desired, stop deserialization.
            Err(DError::FormatSpecTooShort) => Ok(None), // nothing more in the format spec list, stop deserialization
            Err(DError::InputEndedEarly) => Ok(None), // no more input, stop deserialization
            Err(e) => Err(e) // other errors are actually problems
        }
    }
}

struct FieldSequence<'a, 'de: 'a, F: AsRef<str>> {
    de: &'a mut Deserializer<'de, F>,
}

impl<'a, 'de, F: AsRef<str>> FieldSequence<'a, 'de, F> {
    fn new(de: &'a mut Deserializer<'de, F>) -> Self {
        Self { de }
    }
}

impl<'a, 'de, F: AsRef<str>> MapAccess<'de> for FieldSequence<'a, 'de, F> {
    type Error = DError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: de::DeserializeSeed<'de> {
        
        if self.de.curr_field().is_none() {
            return Ok(None)
        }
        
        seed.deserialize(&mut *self.de).map(Some)
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: de::DeserializeSeed<'de> {
        seed.deserialize(&mut *self.de)
    }
}

// --------------------- //
// VISITOR FOR FORTVALUE //
// --------------------- //

pub(crate) struct FortValueVisitor;

impl<'de> Visitor<'de> for FortValueVisitor {
    type Value = FortValue;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("any valid scalar Fortran value")
    }

    fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(FortValue::Logical(v))
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(FortValue::Integer(v))
    }

    fn visit_u8<E>(self, v: u8) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_i64(v.into())
    }

    fn visit_u16<E>(self, v: u16) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_i64(v.into())
    }

    fn visit_u32<E>(self, v: u32) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_i64(v.into())
    }

    fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(FortValue::Real(v))
    }

    fn visit_char<E>(self, v: char) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_str(v.encode_utf8(&mut [0u8; 4]))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(FortValue::Char(v.to_string()))
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_str(v)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(FortValue::Char(v))
    }
}

#[cfg(test)]
mod tests {
    use serde::Deserialize;

    use super::*;

    // ---------------------------------- //
    // Fixed-format deserialization tests //
    // ---------------------------------- //

    #[test]
    fn test_de_bool() -> DResult<()> {
        let ff = FortFormat::parse("(l1)")?;
        let b: bool = from_str("T", &ff)?;
        assert_eq!(b, true);
        Ok(())
    }

    #[test]
    fn test_de_integer() -> DResult<()> {
        let ff = FortFormat::parse("(i2)")?;
        let i: i8 = from_str(" 8", &ff)?;
        assert_eq!(i, 8);

        let i: i8 = from_str("-1", &ff)?;
        assert_eq!(i, -1);

        // this confirms that we only parse two characters - including the sign
        let i: i8 = from_str("-22", &ff)?;
        assert_eq!(i, -2);

        let i: i64 = from_str("42", &ff)?;
        assert_eq!(i, 42);

        let i: i64 = from_str("-7", &ff)?;
        assert_eq!(i, -7);

        let u: u8 = from_str(" 3", &ff)?;
        assert_eq!(u, 3);

        let u: u64 = from_str("26", &ff)?;
        assert_eq!(u, 26);

        // this confirms that we only parse two characters
        let u: u8 = from_str("200", &ff)?;
        assert_eq!(u, 20);

        Ok(())
    }

    #[test]
    fn test_de_float() -> DResult<()> {
        let ff = FortFormat::parse("(f8)")?;
        let r: f64 = from_str("12.45678", &ff)?;
        assert_eq!(r, 12.45678);

        let r: f64 = from_str("-23.5678", &ff)?;
        assert_eq!(r, -23.5678);

        // TODO: Need to test scaled numbers
        // For E/D formats, reading with scales doesn't matter: `write(*, '(2pe13.5)') 0.9`
        //  produces 90.0000E-02, which we can parse as is. The challenge is for F formats,
        //  `write(*, '(2pf13.5)') 0.9` produces 90.00000 i.e. the 2p multiplies the output
        //  by 10^2. G formats seem to ignore the P scaling on output, need to check input.
        let ff = FortFormat::parse("(e8)")?;
        let r: f64 = from_str("1.34E+03", &ff)?;
        assert_eq!(r, 1.34e3);

        let r: f64 = from_str("1.34e+03", &ff)?;
        assert_eq!(r, 1.34e3);

        let r: f64 = from_str("1.34E-03", &ff)?;
        assert_eq!(r, 1.34e-3);

        let r: f64 = from_str("1.34e-03", &ff)?;
        assert_eq!(r, 1.34e-3);

        let ff = FortFormat::parse("(d8)")?;
        let r: f64 = from_str("1.34D+03", &ff)?;
        assert_eq!(r, 1.34e3);

        let r: f64 = from_str("1.34d+03", &ff)?;
        assert_eq!(r, 1.34e3);

        let r: f64 = from_str("1.34D-03", &ff)?;
        assert_eq!(r, 1.34e-3);

        let r: f64 = from_str("1.34d-03", &ff)?;
        assert_eq!(r, 1.34e-3);

        let ff = FortFormat::parse("(2pe13.5)")?;
        let r: f64 = from_str("  90.0000E-02", &ff)?;
        assert_eq!(r, 0.9, "(2pe13.5)");

        let ff = FortFormat::parse("(-2pe13.5)")?;
        let r: f64 = from_str("  0.00900E+02", &ff)?;
        assert_eq!(r, 0.9, "(-2pe13.5)");

        let ff = FortFormat::parse("(2pf13.5)")?;
        let r: f64 = from_str("     90.00000", &ff)?;
        assert_eq!(r, 0.9, "(2pf13.5)");

        let ff = FortFormat::parse("(-2pf13.5)")?;
        let r: f64 = from_str("      0.00800", &ff)?;
        assert_eq!(r, 0.8, "(-2pf13.5)");

        Ok(())
    }

    #[test]
    fn test_de_string() -> DResult<()> {
        let ff = FortFormat::parse("(a16)")?;
        let s: String = from_str("Hello world!    ", &ff)?;
        assert_eq!(s, "Hello world!");

        let settings = DeSettings::default().do_trim(false);
        let s: String = from_str_custom("Hello world!    ", &ff, settings)?;
        assert_eq!(s, "Hello world!    ");
        Ok(())
    }

    #[test]
    fn test_de_tuple() -> DResult<()> {
        let ff = FortFormat::parse("(a1,1x,i2,1x,i4)")?;
        let t: (char, i32, i32) = from_str("a 16 9876", &ff)?;
        assert_eq!(t, ('a', 16, 9876));
        Ok(())
    }

    #[test]
    fn test_de_vec() -> DResult<()> {
        let ff = FortFormat::parse("5(i3,1x)")?;
        let v: Vec<i32> = from_str("123 456 789 246 369", &ff)?;
        assert_eq!(&v, &[123, 456, 789, 246, 369]);
        Ok(())
    }

    #[test]
    fn test_de_vec_in_tuple() -> DResult<()> {
        let ff = FortFormat::parse("(a5,1x,3i3,a5)")?;
        let t: (String, Vec<i32>, String) = from_str("Hello 12 34 56 World", &ff)?;
        assert_eq!(t, ("Hello".to_owned(), vec![12, 34, 56], "World".to_owned()));
        Ok(())
    }

    #[test]
    fn test_de_struct() -> DResult<()> {
        #[derive(Debug, PartialEq, Eq, Deserialize)]
        struct Test {
            x: i32,
            y: i32,
            c: char,
            b: bool
        }

        let ff = FortFormat::parse("(2i3,1x,a,1x,l1)")?;
        let s: Test = from_str(" 10 20 z F", &ff)?;
        assert_eq!(s, Test { x: 10, y: 20, c: 'z', b: false });

        Ok(())
    }

    #[test]
    fn test_de_struct_with_array() -> DResult<()> {
        #[derive(Debug, PartialEq, Eq, Deserialize)]
        struct Test {
            flag: bool,
            data: [i32; 8]
        }

        let ff = FortFormat::parse("(l1,1x,8i3)")?;
        let s: Test = from_str("T  10 20 30 40 50 60 70 80", &ff)?;
        assert_eq!(s, Test{ flag: true, data: [10, 20, 30, 40, 50, 60, 70, 80] });

        Ok(())
    }

    #[test]
    fn test_de_struct_with_fields() -> DResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Test {
            alpha: i32,
            beta: f64,
            gamma: String,
        }

        let ff = FortFormat::parse("(a8,1x,i4,1x,f5.3)")?;
        let fields = ["gamma", "alpha", "beta"];
        let s: Test = from_str_with_fields(
            "abcdefgh 1234 9.876", 
            &ff, 
            &fields
        )?;

        assert_eq!(s, Test{ alpha: 1234, beta: 9.876, gamma: "abcdefgh".to_string() });

        Ok(())
    }

    #[test]
    fn test_de_struct_with_inner_struct() -> DResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Inner {
            x: i32,
            y: i32,
        }

        #[derive(Debug, PartialEq, Deserialize)]
        struct Outer {
            sid: String,
            #[serde(flatten)]
            coords: Inner,
            flag: i8,
        }

        let ff = FortFormat::parse("(a2,1x,i1,1x,i3,1x,i3)")?;
        let fields = ["sid", "flag", "y", "x"];
        let s: Outer = from_str_with_fields(
            "pa 0 456 123",
            &ff,
            &fields
        )?;

        assert_eq!(s, Outer{ sid: "pa".to_string(), flag: 0, coords: Inner { x: 123, y: 456 } });

        Ok(())
    }

    #[test]
    fn test_de_inner_struct_not_flattened() -> DResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Inner {
            x: i32,
            y: i32,
        }

        #[derive(Debug, PartialEq, Deserialize)]
        struct Outer {
            sid: String,
            coords: Inner,
            flag: i8,
        }

        let ff = FortFormat::parse("(a2,1x,i1,1x,i3,1x,i3)")?;
        let fields = ["sid", "flag", "y", "x"];
        let s: DResult<Outer> = from_str_with_fields(
            "pa 0 456 123",
            &ff,
            &fields
        );

        // Note: I wrote this to test for an error because as of 2023-10-20 I'm assuming that
        // serde will try to deserialize something for the "coords" field itself, and there's
        // no way to tell the Fortran deserializer that it shouldn't advance the format & field
        // indices in that case (without using the #[serder(flatten)] tag). But this deserialization
        // calls `deserialize_ignored_any` (unclear for which field), so there may be a mechanism
        // to handle this test case correctly.
        //
        // On the other hand, using #[serde(flatten)] is clearer that the fields of an inner struct
        // should be deserialized as if they are directly in the outer struct.
        assert!(s.is_err());

        Ok(())
    }

    #[test]
    fn test_extra_fields_map() -> DResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Test {
            name: String,
            flag: i8,
            #[serde(flatten)]
            gases: std::collections::HashMap<String, f32>
        }

        let ff = FortFormat::parse("(a5,1x,i1,1x,f6.2,1x,f6.1,1x,f6.2)")?;
        let fields = ["name", "flag", "co2", "ch4", "n2o"];
        let data = "spec1 0 432.10 1800.0  98.76";
        let s: Test = from_str_with_fields(data, &ff, &fields)?;

        let gases = std::collections::HashMap::from([
            ("co2".to_string(), 432.10),
            ("ch4".to_string(), 1800.0),
            ("n2o".to_string(), 98.76) 
        ]);

        let expected = Test { name: "spec1".to_string(), flag: 0, gases };
        assert_eq!(s, expected);

        Ok(())
    }

    #[test]
    fn test_middle_opt_field() -> DResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Test {
            a: i32,
            b: Option<i32>,
            c: i32
        }

        let ff = FortFormat::parse("(i2,i2)")?;
        let fields = ["a", "c"];
        let data = " 1 2";
        let s: Test = from_str_with_fields(&data, &ff, &fields)?;
        
        let expected = Test { a: 1, b: None, c: 2 };
        assert_eq!(s, expected, "Deserializing struct with missing optional field failed with fixed format");

        let s: Test = from_str_with_fields(&data, &FortFormat::ListDirected, &fields)?;
        assert_eq!(s, expected, "Deserializing struct with missing optional field failed with list-directed format");

        Ok(())
    }

    #[test]
    fn test_middle_opt_field_missing_by_name() -> DResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Test {
            a: i32,
            b: Option<i32>,
            c: i32
        }

        let ff = FortFormat::parse("(i2,1x,a4,1x,i2)")?;
        let fields = ["a", "skip", "c"];
        let data = "10 abcd 20";
        let s: Test = from_str_with_fields(&data, &ff, &fields)?;
        
        let expected = Test { a: 10, b: None, c: 20 };
        assert_eq!(s, expected, "Deserializing struct with missing optional field failed with fixed format");

        let s: Test = from_str_with_fields(&data, &FortFormat::ListDirected, &fields)?;
        assert_eq!(s, expected, "Deserializing struct with missing optional field failed with list-directed format");

        Ok(())
    }

    #[test]
    fn test_de_scalar_fort_value() -> DResult<()> {
        let v: FortValue = from_str("T", &FortFormat::parse("(l1)")?)?;
        assert_eq!(v, FortValue::Logical(true));

        let v: FortValue = from_str("123", &FortFormat::parse("(i3)")?)?;
        assert_eq!(v, FortValue::Integer(123));

        let v: FortValue = from_str("-456", &FortFormat::parse("(i4)")?)?;
        assert_eq!(v, FortValue::Integer(-456));

        let v: FortValue = from_str("9.5", &FortFormat::parse("(f3.1)")?)?;
        assert_eq!(v, FortValue::Real(9.5));

        let v: FortValue = from_str("abcde", &FortFormat::parse("(a5)")?)?;
        assert_eq!(v, FortValue::Char("abcde".to_string()));

        Ok(())
    }

    #[test]
    fn test_de_vector_fort_values() -> DResult<()> {
        let ff = FortFormat::parse("(l1,1x,i3,1x,i4,1x,f4.1,1x,a5)")?;
        let v: Vec<FortValue> = from_str("F 987 -123 -1.5 ZYXWV", &ff)?;
        let expected = vec![
            FortValue::Logical(false),
            FortValue::Integer(987),
            FortValue::Integer(-123),
            FortValue::Real(-1.5),
            FortValue::Char("ZYXWV".to_string())
        ];
        assert_eq!(v, expected);
        Ok(())
    }

    // ----------------------------------- //
    // List-directed deserialization tests //
    // ----------------------------------- //

    #[test]
    fn test_list_de_int() -> DResult<()> {
        let ff = FortFormat::ListDirected;

        let vspace: (i32, i32, i32) = from_str("1 2 34", &ff)?;
        assert_eq!(vspace, (1, 2, 34));

        // The space around the second comma is deliberate - " , " should
        // be treated as one separator.
        let vcomma: (i32, i32, i32) = from_str("4, 56 , 7", &ff)?;
        assert_eq!(vcomma, (4, 56, 7));

        Ok(())
    }

    #[test]
    fn test_list_de_vector_int() -> DResult<()> {
        let ff = FortFormat::ListDirected;
        let vspace: Vec<i32> = from_str("1 2 34", &ff)?;
        assert_eq!(vspace, vec![1, 2, 34]);

        // The space around the second comma is deliberate - " , " should
        // be treated as one separator.
        let vcomma: Vec<i32> = from_str("4, 56 , 7", &ff)?;
        assert_eq!(vcomma, vec![4, 56, 7]);

        Ok(())
    }

    #[test]
    fn test_list_de_str() -> DResult<()> {
        let ff = FortFormat::ListDirected;
        let vspace: (&str, &str) = from_str(r#"hello "my beautiful" world"#, &ff)?;
        assert_eq!(vspace, ("hello", "my beautiful"));

        let vcomma: (&str, &str, &str) = from_str("goodbye 'my frigid' world ", &ff)?;
        assert_eq!(vcomma, ("goodbye", "my frigid", "world"));

        let v_first_quote: &str = from_str("'who else' 1 2 3", &ff)?;
        assert_eq!(v_first_quote, "who else");

        let v_last_quote: (&str, &str) = from_str("and 'last but not least'", &ff)?;
        assert_eq!(v_last_quote.1, "last but not least");

        Ok(())
    }

    #[test]
    fn test_list_de_structs() -> DResult<()> {
        let ff = FortFormat::ListDirected;

        // All three tests in this function are based on a real use case in GGG code
        // First test: a structure where all fields are expected to be provided.
        #[derive(Debug, Deserialize, PartialEq)]
        struct InsituCorr<'a> {
            #[serde(rename="Gas")]
            gas: &'a str,
            #[serde(rename="AICF")]
            aicf: f64,
            #[serde(rename="AICF_Err")]
            aicf_err: f64,
            #[serde(rename="WMO_Scale")]
            wmo_scale: &'a str
        }

        let s1de: InsituCorr = from_str_with_fields(
            r#""xco2"   1.0101  0.0005  "WMO CO2 X2007""#,
            &ff,
            &["Gas", "AICF", "AICF_Err", "WMO_Scale"]
        )?;

        let s1true = InsituCorr {
            gas: "xco2",
            aicf: 1.0101,
            aicf_err: 0.0005,
            wmo_scale: "WMO CO2 X2007",
        };

        assert_eq!(s1de, s1true, "Deserialized InsituCorr test structure produced different values than expected.");


        // Second test: a structure where the last fields may be omitted, but in this
        // case they are provided.
        #[derive(Debug, Deserialize, PartialEq)]
        struct AirmassCorr<'a> {
            #[serde(rename="Gas")]
            gas: &'a str,
            #[serde(rename="ADCF")]
            adcf: f64,
            #[serde(rename="ADCF_Err")]
            adcf_err: f64,
            g: Option<f64>,
            p: Option<f64>
        }

        let s2de: AirmassCorr = from_str_with_fields(
            r#""xco2_6220"  -0.00903  0.00025   15   4"#,
            &ff,
            &["Gas", "ADCF", "ADCF_Err", "g", "p"]
        )?;

        let s2true = AirmassCorr{
            gas: "xco2_6220",
            adcf: -0.00903,
            adcf_err: 0.00025,
            g: Some(15.0),
            p: Some(4.0)
        };

        assert_eq!(s2de, s2true, "Deserializing AirmassCorr with the g and p values produced different values than expected.");

        // Third test: a structure where the last fields may be omitted and are omitted.
        // Also tests a line with whitespace at the end.
        let s3de: AirmassCorr = from_str_with_fields(
            r#""xco2"  -0.0068  0.0050   "#,
            &ff,
            &["Gas", "ADCF", "ADCF_Err"]
        )?;

        let s3true = AirmassCorr{
            gas: "xco2",
            adcf: -0.0068,
            adcf_err: 0.005,
            g: None,
            p: None
        };

        assert_eq!(s3de, s3true, "Deserialized AirmassCorr without the g and p value produced different values than expected.");
        Ok(())
    }
}
