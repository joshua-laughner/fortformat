//! Errors in serializing/deseralizing Fortran-formatted data
use std::string::FromUtf8Error;
use std::{fmt::Display, error::Error};
use serde::{ser, de};
use crate::format_specs::{FortField, PError};
use crate::fort_error::FError;

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