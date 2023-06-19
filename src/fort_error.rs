use std::fmt::Display;
use pest::RuleType;

pub type FResult<T> = Result<T, FError>;

#[derive(Debug)]
pub enum FError {
    ParsingError{ s: String, t: &'static str, reason: String },
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