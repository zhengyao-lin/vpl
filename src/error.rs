// Error types and their conversions

use thiserror::Error;
use crate::parser::ParserError;
use crate::trace::TraceError;

#[derive(Error, Debug)]
/// Aggregate all errors in main()
pub enum Error {
    #[error("IO error: {0}")]
    IOError(#[from] std::io::Error),

    #[error("parse error: {0}")]
    ParseError(ParserError),

    #[error("trace validation error: {0}")]
    TraceError(TraceError),

    #[error("{0}")]
    Other(String),
}

impl From<TraceError> for Error {
    fn from(err: TraceError) -> Self {
        Error::TraceError(err)
    }
}

impl From<ParserError> for Error {
    fn from(err: ParserError) -> Self {
        Error::ParseError(err)
    }
}
