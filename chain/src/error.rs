use thiserror::Error;

use parser::common::ParseError as X509ParseError;
use vpl::checker::ProofError;
use vpl::parser::ParserError as VPLParserError;
use vpl::error::Error as VPLError;
use crate::specs::ValidationError;

#[derive(Error, Debug)]
/// Aggregate all errors in main()
pub enum Error {
    #[error("IO error: {0}")]
    IOError(#[from] std::io::Error),

    #[error("x509 parse error: {0:?}")]
    X509ParseError(X509ParseError),

    #[error("validation error: {0:?}")]
    ValidationError(ValidationError),

    #[error("vpl parse error: {0}")]
    VPLParserError(VPLParserError),

    #[error("vpl error: {0}")]
    VPLError(VPLError),

    #[error("proof error: {0}")]
    ProofError(ProofError),

    #[error("{0}")]
    Other(String),
}

impl From<X509ParseError> for Error {
    fn from(err: X509ParseError) -> Self {
        Error::X509ParseError(err)
    }
}

impl From<ValidationError> for Error {
    fn from(err: ValidationError) -> Self {
        Error::ValidationError(err)
    }
}

impl From<VPLParserError> for Error {
    fn from(err: VPLParserError) -> Self {
        Error::VPLParserError(err)
    }
}

impl From<VPLError> for Error {
    fn from(err: VPLError) -> Self {
        Error::VPLError(err)
    }
}

impl From<ProofError> for Error {
    fn from(err: ProofError) -> Self {
        Error::ProofError(err)
    }
}
