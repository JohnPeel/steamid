use core::fmt;

use displaydoc::Display;

use super::AccountType;

/// Error type for crate.
#[derive(Debug, Display)]
pub enum Error {
    /// invalid universe: {0}
    InvalidUniverse(InvalidValue<u8>),
    /// invalid account type: {0}
    InvalidAccountType(InvalidValue<u8>),
    /// invalid chat flags: {0}
    InvalidChatFlags(InvalidValue<u32>),
    /// invalid instance: {0}
    InvalidInstance(InvalidValue<u32>),
    /// invalid account number: {0}
    InvalidAccountNumber(InvalidValue<u32>),
    /// invalid auth server: {0}
    InvalidAuthServer(InvalidValue<u8>),
    /// account type does not have a character representation: {0:?}
    NoCharacterRepresentation(InvalidValue<AccountType>),
    /// character representation is not a valid account type: {0}
    InvalidCharacterRepresentation(InvalidValue<char>),

    /// parse error: {0}
    ParseError(&'static str),
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// Represents an invalid value.
#[derive(Clone, Copy, Debug)]
pub struct InvalidValue<T>(T);

impl<T> InvalidValue<T> {
    #[must_use]
    pub(crate) const fn new(value: T) -> Self {
        Self(value)
    }

    /// Returns a reference to the inner `T`.
    #[must_use]
    pub const fn as_inner(&self) -> &T {
        &self.0
    }

    /// Returns the inner `T`.
    #[must_use]
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T: fmt::Display> fmt::Display for InvalidValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_inner().fmt(f)
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> std::error::Error for InvalidValue<T> {}
