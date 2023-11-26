//! Errors in Fortran format strings or values
use std::fmt::Display;
use pest::RuleType;

/// Type alias for a `Result` with [`FError`] as the error type.
pub type FResult<T> = Result<T, FError>;


/// An error related to a Fortran format specification
#[derive(Debug)]
pub enum FError {
    /// Indicates an error parsing a data substring as a given type.
    ParsingError{ s: String, t: &'static str, reason: String },

    /// Indicates that a string passed as a Fortran format specification
    /// had no actual fields.
    EmptyExpression(String)
}

impl Display for FError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FError::ParsingError { s, t, reason } => {
                write!(f, "Could not parse '{s}' as a {t}: {reason}")
            },
            FError::EmptyExpression(expr) => {
                write!(f, "Empty expression: '{expr}'")
            }
        }
    }
}

impl std::error::Error for FError {}

impl FError {
    pub fn from_pest<R: RuleType>(e: pest::error::Error<R>, s: String, t: &'static str) -> Self {
        Self::ParsingError { s, t, reason: e.to_string() }
    }
}