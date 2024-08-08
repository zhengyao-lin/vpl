// Error types and their conversions

use thiserror::Error;
use crate::parser::ParserError;
use crate::trace::{TraceError, EventId};

#[derive(Error, Debug)]
/// Aggregate all errors in main()
pub enum Error {
    #[error("IO error: {0}")]
    IOError(#[from] std::io::Error),

    #[error("parse error at {0}: {1}")]
    ParseError(String, String),

    #[error("trace validation error at event {0}: {1}")]
    TraceError(EventId, String),

    #[error("{0}")]
    Other(String),
}

impl From<TraceError> for Error {
    fn from(err: TraceError) -> Self {
        Error::TraceError(err.0, err.1)
    }
}

impl From<ParserError> for Error {
    fn from(err: ParserError) -> Self {
        // TODO: refactor this
        let path = err.0.unwrap_or("<unknown>".to_string());
        Error::ParseError(format!("{}:{}:{}", path, err.1.location.line, err.1.location.column), err.1.expected.to_string())
    }
}
