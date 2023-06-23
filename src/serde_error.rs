use std::{fmt::Display, error::Error};
use serde::{ser, de};
use crate::format_specs::{FortField, PError};
use crate::fort_error::FError;

pub type SResult<T> = Result<T, SError>;

#[derive(Debug)]
pub enum SError {
    FormatSpecTooShort,
    FormatTypeMismatch{spec_type: FortField, serde_type: &'static str},
    InputEndedEarly,
    ParsingError(FError),
    FormatError(PError),
    DeserializationFailure(String)
}

impl SError {
    pub fn with_serde_type(self, serde_type: &'static str) -> Self {
        match self {
            Self::FormatTypeMismatch { spec_type, serde_type: _ } => Self::FormatTypeMismatch { spec_type, serde_type },
            _ => self
        }
    }
}

impl Display for SError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SError::FormatSpecTooShort => write!(f, "Format specifier ended before all fields of the structure to deserialize into were filled."),
            SError::FormatTypeMismatch { spec_type, serde_type } => write!(f, "The next value in the format specifier was {spec_type}, but the structure to deserialize into expected a {serde_type}"),
            SError::InputEndedEarly => write!(f, "The input ended before deserialization was complete"),
            SError::ParsingError(e) => write!(f, "Error parsing value: {e}"),
            SError::FormatError(e) => write!(f, "Error parsing format: {e}"),
            SError::DeserializationFailure(msg) => write!(f, "Serde deserialization error: {msg}"),
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