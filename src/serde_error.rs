//! Errors in serializing/deseralizing Fortran-formatted data
use std::{fmt::Display, error::Error};
use serde::{ser, de};
use crate::format_specs::{FortField, PError};
use crate::fort_error::FError;

/// A type alias for `Result` with [`SError`] as the error type.
pub type SResult<T> = Result<T, SError>;

/// Errors that can occur while deserializing data with a Fortran format.
#[derive(Debug)]
pub enum SError {
    /// Indicates that the Fortran format string ended before all values/fields were deserialized.
    FormatSpecTooShort,
    /// Indicates a mismatch between the Rust type expected and the Fortran type in the specification.
    FormatTypeMismatch{spec_type: FortField, serde_type: &'static str},
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

impl SError {
    pub(crate) fn with_serde_type(self, serde_type: &'static str) -> Self {
        match self {
            Self::FormatTypeMismatch { spec_type, serde_type: _ } => Self::FormatTypeMismatch { spec_type, serde_type },
            _ => self
        }
    }
}

impl Display for SError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FormatSpecTooShort => write!(f, "Format specifier ended before all fields of the structure to deserialize into were filled."),
            Self::FormatTypeMismatch { spec_type, serde_type } => write!(f, "The next value in the format specifier was {spec_type}, but the structure to deserialize into expected a {serde_type}"),
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

impl ser::Error for SError {
fn custom<T>(msg:T) -> Self where T:Display {
        todo!()
    }
}

impl de::Error for SError {
fn custom<T>(msg:T) -> Self where T:Display {
        Self::DeserializationFailure(format!("{msg}"))
    }
}

impl Error for SError {}

impl From<FError> for SError {
    fn from(value: FError) -> Self {
        Self::ParsingError(value)
    }
}

impl From<PError> for SError {
    fn from(value: PError) -> Self {
        Self::FormatError(value)
    }
}