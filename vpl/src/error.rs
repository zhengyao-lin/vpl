// Error types and their conversions
use crate::checker::ProofError;
use crate::parser::ParseError;
use std::num::TryFromIntError;
use thiserror::Error;

#[derive(Error, Debug)]
/// Aggregate all errors in main()
pub enum Error {
    #[error("IO error: {0}")]
    IOError(#[from] std::io::Error),

    #[error("parse error: {0}")]
    ParseError(ParseError),

    #[error("proof error: {0}")]
    ProofError(ProofError),

    #[error("Backend succeeded but failed to produce a valid proof")]
    NoMatchingProof,

    #[error("Backend failed to prove the goal")]
    BackendFailure,
}

impl From<ProofError> for Error {
    fn from(err: ProofError) -> Self {
        Error::ProofError(err)
    }
}

impl From<ParseError> for Error {
    fn from(err: ParseError) -> Self {
        Error::ParseError(err)
    }
}

impl From<TryFromIntError> for ProofError {
    fn from(err: TryFromIntError) -> Self {
        ProofError(format!("failed to convert integer: {}", err))
    }
}
