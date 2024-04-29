//! Errors in serializing/deseralizing Fortran-formatted data
use std::string::FromUtf8Error;
use std::sync::Arc;
use std::{fmt::Display, error::Error};
use serde::{ser, de};
use crate::format_specs::{FortField, IntBase, PError, RealFmt};
use crate::fort_error::FError;
use crate::ser::{serialize_characters, serialize_integer, serialize_logical, serialize_real_exp, serialize_real_f};

/// A type alias for `Result` with [`SError`] as the error type.
pub type SResult<T> = Result<T, SError>;

/// Errors that can occur while serializing data with a Fortran format
#[derive(Debug)]
pub enum SError {
    /// Indicates that the Fortran format string ended before all values/fields were serialized.
    FormatSpecTooShort,
    /// Indicates a mismatch between the Rust type given and the Fortran type in the specification.
    FormatTypeMismatch{spec_type: FortField, serde_type: &'static str, field_name: Option<String>},
    /// Indicates a problem parsing a Fortran format string or value
    ParsingError(FError),
    /// Indicates an invalid format in a Fortran format string
    FormatError(PError),
    /// Indicates an error writing the data
    WriteError(std::io::Error),
    /// Indicates that a format cannot be used for output
    InvalidOutputFmt(FortField, String),
    /// Indicates that an arbitrary key could not be converted to a string when matching up with fields
    KeyToFieldError(Arc<Self>),
    /// Indicates that a field name/key could not be found in the list of fields
    FieldMissingError(String),
    /// Indicates a failure during serialization
    SerializationFailure(String),
    /// Indicates that the buffered bytes could not be converted to a UTF8 string
    UnicodeError(FromUtf8Error),
}

impl Display for SError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FormatSpecTooShort => write!(f, "Format specifier ended before all fields of the structure to deserialize into were filled."),
            Self::FormatTypeMismatch { spec_type, serde_type, field_name } => {
                if let Some(field) = field_name {
                    write!(f, "The next value in the format specifier for the field '{field}' was {spec_type}, but the structure to deserialize into expected a {serde_type}")
                } else {
                    write!(f, "The next value in the format specifier was {spec_type}, but the structure to deserialize into expected a {serde_type}")
                }
            },
            Self::ParsingError(e) => write!(f, "Error parsing value: {e}"),
            Self::FormatError(e) => write!(f, "Error parsing format: {e}"),
            Self::WriteError(e) => write!(f, "Error writing data: {e}"),
            Self::InvalidOutputFmt(field, msg) => write!(f, "'{field} is not valid for an output format: {msg}"),
            Self::KeyToFieldError(e) => write!(f, "Unable to convert one of the map keys to a string to compare with field names, error was: {e}"),
            Self::FieldMissingError(field) => write!(f, "Unable to find the field '{field}' in the list of field names"),
            Self::SerializationFailure(msg) => write!(f, "Error serializing data: {msg}"),
            Self::UnicodeError(e) => write!(f, "Serialized data includes invalid unicode: {e}")
        }
    }
}

impl Error for SError {}

impl ser::Error for SError {
fn custom<T>(msg:T) -> Self where T:Display {
        Self::SerializationFailure(msg.to_string())
    }
}

impl From<std::io::Error> for SError {
    fn from(value: std::io::Error) -> Self {
        Self::WriteError(value)
    }
}

impl From<FromUtf8Error> for SError {
    fn from(value: FromUtf8Error) -> Self {
        Self::UnicodeError(value)
    }
}

/// A type alias for `Result` with [`DError`] as the error type.
pub type DResult<T> = Result<T, DError>;

/// Errors that can occur while deserializing data with a Fortran format.
#[derive(Debug)]
pub enum DError {
    /// Indicates that the Fortran format string ended before all values/fields were deserialized.
    FormatSpecTooShort,
    /// Indicates a mismatch between the Rust type expected and the Fortran type in the specification.
    FormatTypeMismatch{spec_type: FortField, serde_type: &'static str, field_name: Option<String>},
    /// Indicates that the list of field names aligned with the Fortran data ended before all fields were deserialized.
    FieldListTooShort,
    /// Indicates that the data given ended before all values/fields were deserialized.
    InputEndedEarly,
    /// Indicates a problem parsing a Fortran format string or value
    ParsingError(FError),
    /// Indicates an invalid format in a Fortran format string
    FormatError(PError),
    /// Indicates a general error during deserialization
    DeserializationFailure(String),
    /// Indicates that there was an I/O error while reading in a line from a file with a data table.
    TableReadError(std::io::Error, usize),
    /// Indicates that a line in a data table ended before all expected columns were deserialized.
    TableLineEndedEarly{line_num: usize, ncol: usize},
}

impl DError {
    pub(crate) fn with_serde_type(self, serde_type: &'static str) -> Self {
        match self {
            Self::FormatTypeMismatch { spec_type, serde_type: _ , field_name} => Self::FormatTypeMismatch { spec_type, serde_type, field_name },
            _ => self
        }
    }
}

impl Display for DError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FormatSpecTooShort => write!(f, "Format specifier ended before all fields of the structure to deserialize into were filled."),
            Self::FormatTypeMismatch { spec_type, serde_type, field_name } => {
                if let Some(field) = field_name {
                    write!(f, "The next value in the format specifier for the field '{field}' was {spec_type}, but the structure to deserialize into expected a {serde_type}")
                } else {
                    write!(f, "The next value in the format specifier was {spec_type}, but the structure to deserialize into expected a {serde_type}")
                }
            },
            Self::FieldListTooShort => write!(f, "Field list ended before all fields of the structure to deserialize into were filled"),
            Self::InputEndedEarly => write!(f, "The input ended before deserialization was complete"),
            Self::ParsingError(e) => write!(f, "Error parsing value: {e}"),
            Self::FormatError(e) => write!(f, "Error parsing format: {e}"),
            Self::DeserializationFailure(msg) => write!(f, "Serde deserialization error: {msg}"),
            Self::TableReadError(e, line_num) => write!(f, "Error reading line {line_num} of table data: {e}"),
            Self::TableLineEndedEarly{line_num, ncol} => write!(f, "Line {line_num} of table data ended before all {ncol} columns were read")
        }
    }
}

impl de::Error for DError {
fn custom<T>(msg:T) -> Self where T:Display {
        Self::DeserializationFailure(format!("{msg}"))
    }
}

impl Error for DError {}

impl From<FError> for DError {
    fn from(value: FError) -> Self {
        Self::ParsingError(value)
    }
}

impl From<PError> for DError {
    fn from(value: PError) -> Self {
        Self::FormatError(value)
    }
}


/// A enum that describes how fill values are created or interpreted.
/// 
/// When serializing data, this is used to decide how to write `None` values,
/// the unit type, and unit structs to the output. When deserializing, it
/// is used to determine whether an `Option` value should be `Some` or
/// `None`. (It is not needed for deseralizing unit types/structs.)
#[derive(Debug, Clone)]
pub enum NoneFill {
    /// This variant will represent fill values with a single character
    /// repeated to fill the width of the field. This is the default,
    /// with an `*` as the character.
    RepChar(u8),

    /// This variant will represent fill values with a string. If the
    /// string is shorter than the field width, it is truncated.
    String(Vec<u8>),

    /// This variant takes an integer and float fill value, and will
    /// serialize those values for fills. Other field types will be
    /// filled as in the `RepChar` variant.
    PartialTyped{int: i64, real: f64, fill_byte: u8},

    /// This variant takes a specific fill value for each possible
    /// Fortran type. The string/character fill will be truncated
    /// if it is longer than the field; the others may overflow
    /// and print as `*`s if the field is not wide enough.
    Typed{logical: bool, int: i64, real: f64, string: Vec<u8>},
}

impl Default for NoneFill {
    fn default() -> Self {
        Self::default_inner()
    }
}

impl NoneFill {
    pub(crate) const fn default_inner() -> Self {
        // need a const default function for the static default serialization settings.
        Self::RepChar(b'*')
    }

    /// Create a new `NoneFill::RepChar` instance with `c` as the fill byte.
    /// 
    /// Note that `c` must be a character which can be written as one byte -
    /// usually this means it must be an ASCII character. If it is not, 
    /// this function will return an error.
    pub fn new_rep_char(c: char) -> Result<Self, std::char::TryFromCharError> {
        let byte: u8 = c.try_into()?;
        Ok(Self::RepChar(byte))
    }

    /// Create a new `NoneFill::String` instance with `s` as the fill string.
    /// 
    /// Note that `s` is converted to bytes internally, and as with all Fortran
    /// character fields, it is the number of bytes that is compared against the
    /// field width when determining if the string must be truncated.
    /// 
    /// Using only ASCII characters is recommended.
    pub fn new_string(s: &str) -> Self {
        let bytes = s.as_bytes().to_vec();
        Self::String(bytes)
    }

    /// Create a new `NoneFill:PartialTyped` instance with `int` as the integer fill and `real` as the real/float fill.
    /// 
    /// This will always use `*` as the fill byte for other field types. If you wish to
    /// use a different fill byte, construct this variant directly.
    pub fn new_partial_typed(int: i64, real: f64) -> Self {
        let fill_byte = '*'.try_into().expect("Should be able to convert a * into a single byte");
        Self::PartialTyped { int, real, fill_byte }
    }

    /// Create a new `NoneFill:Typed` instance with fill values for each of the four Fortran types.
    pub fn new_typed(logical: bool, int: i64, real: f64, string: &str) -> Self {
        let string = string.as_bytes().to_vec();
        Self::Typed { logical, int, real, string }
    }

    pub(crate) fn make_fill_bytes(&self, fmt: &FortField, left_align_str: bool) -> SResult<Vec<u8>> {
        match self {
            NoneFill::RepChar(byte) => Ok(Self::_fill_bytes_rep_char(*byte, fmt.width())),
            NoneFill::String(bytes) => Self::_file_bytes_string(bytes, Some(fmt.width()), left_align_str),
            NoneFill::PartialTyped { int, real, fill_byte } => {
                match fmt {
                    FortField::Char { width } => Ok(Self::_fill_bytes_rep_char(*fill_byte, width.unwrap_or(1))),
                    FortField::Logical { width } => Ok(Self::_fill_bytes_rep_char(*fill_byte, *width)),
                    FortField::Integer { width, zeros, base } => Self::_fill_bytes_int(*int, *width, *zeros, *base),
                    FortField::Real { width, precision, fmt, scale } => {
                        let precision = precision.expect("Format strings for real values must include a precision when writing");
                        Self::_fill_bytes_real(*real, *fmt, *width, precision, *scale)
                    },
                    FortField::Skip => panic!("make_fill_bytes called on a positional format field"),
                }
            },
            NoneFill::Typed { logical, int, real, string } => {
                match fmt {
                    FortField::Char { width } => Self::_file_bytes_string(&string, *width, left_align_str),
                    FortField::Logical { width } => Self::_fill_bytes_logical(*logical, *width),
                    FortField::Integer { width, zeros, base } => Self::_fill_bytes_int(*int, *width, *zeros, *base),
                    FortField::Real { width, precision, fmt, scale } => {
                        let precision = precision.expect("Format strings for real values must include a precision when writing");
                        Self::_fill_bytes_real(*real, *fmt, *width, precision, *scale)
                    },
                    FortField::Skip => panic!("make_fill_bytes called on a positional format field"),
                }
            },
        }
    }

    fn _fill_bytes_rep_char(byte: u8, width: u32) -> Vec<u8> {
        std::iter::repeat(byte).take(width as usize).collect()
    }

    fn _file_bytes_string(bytes: &[u8], width: Option<u32>, left_aligned: bool) -> SResult<Vec<u8>> {
        let mut buf = vec![];
        serialize_characters(bytes, width, &mut buf, left_aligned)?;
        Ok(buf)
    }

    fn _fill_bytes_logical(fill_bool: bool, width: u32) -> SResult<Vec<u8>> {
        let mut buf = vec![];
        serialize_logical(fill_bool, width, &mut buf)?;
        Ok(buf)
    }

    fn _fill_bytes_int(fill_int: i64, width: u32, zeros: Option<u32>, base: IntBase) -> SResult<Vec<u8>> {
        let mut buf: Vec<u8> = vec![];
        let abs_value = fill_int.abs();
        let is_neg = fill_int < 0;
        serialize_integer(width, zeros, base, &mut buf, abs_value, is_neg)?;
        Ok(buf)
    }

    fn _fill_bytes_real(fill_real: f64, real_kind: RealFmt, width: u32, precision: u32, scale: i32) -> SResult<Vec<u8>> {
        let mut buf: Vec<u8> = vec![];

        match real_kind {
            RealFmt::D => serialize_real_exp(&mut buf, fill_real, width, precision, scale, "D", None)?,
            RealFmt::E => serialize_real_exp(&mut buf, fill_real, width, precision, scale, "E", None)?,
            RealFmt::F => serialize_real_f(&mut buf, fill_real, width, precision, scale)?,
            RealFmt::G => todo!(),
        }

        Ok(buf)
    }
}