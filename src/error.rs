// Error types and their conversions

use thiserror::Error;
use crate::parser::ParserError;
use crate::checker::ProofError;
use std::num::TryFromIntError;

#[derive(Error, Debug)]
/// Aggregate all errors in main()
pub enum Error {
    #[error("IO error: {0}")]
    IOError(#[from] std::io::Error),

    #[error("parse error: {0}")]
    ParseError(ParserError),

    #[error("proof error: {0}")]
    ProofError(ProofError),

    #[error("{0}")]
    Other(String),
}

impl From<ProofError> for Error {
    fn from(err: ProofError) -> Self {
        Error::ProofError(err)
    }
}

impl From<ParserError> for Error {
    fn from(err: ParserError) -> Self {
        Error::ParseError(err)
    }
}

impl From<TryFromIntError> for ProofError {
    fn from(err: TryFromIntError) -> Self {
        ProofError(format!("failed to convert integer: {}", err))
    }
}
