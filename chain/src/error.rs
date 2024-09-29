use parser::common::ParseError;
use thiserror::Error;

#[derive(Error, Debug)]
/// Aggregate all errors in main()
pub enum Error {
    #[error("IO error: {0}")]
    IOError(#[from] std::io::Error),

    #[error("parse error: {0:?}")]
    ParseError(ParseError),

    #[error("{0}")]
    Other(String),
}

impl From<ParseError> for Error {
    fn from(err: ParseError) -> Self {
        Error::ParseError(err)
    }
}
