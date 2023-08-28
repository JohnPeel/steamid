use displaydoc::Display;
use from_enum::From;

// Allow these to be unused as we use them in the macro to construct names.
// Clippy still considers them unused though.
#[allow(unused_imports)]
use super::{AccountId, AccountNumber, AccountType, AuthServer, ChatFlags, Instance, Universe};

/// Error type for crate.
#[derive(Debug, Display, From)]
pub enum Error {
    /// invalid universe: {0}
    InvalidUniverse(#[from] InvalidUniverse),
    /// invalid account type: {0}
    InvalidAccountType(#[from] InvalidAccountType),
    /// invalid chat flags: {0}
    InvalidChatFlags(#[from] InvalidChatFlags),
    /// invalid instance: {0}
    InvalidInstance(#[from] InvalidInstance),
    /// invalid account number: {0}
    InvalidAccountNumber(#[from] InvalidAccountNumber),
    /// invalid auth server: {0}
    InvalidAuthServer(#[from] InvalidAuthServer),

    /// account type does not have a character representation: {0:?}
    NoCharacterRepresentation(AccountType),
    /// character representation is not a valid account type: {0}
    InvalidCharacterRepresentation(char),
    /// parse error: {0}
    ParseError(&'static str),
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// Result type for crate.
pub type Result<T, E = Error> = core::result::Result<T, E>;

macro_rules! into_error {
    ($($ty:ty => $prim:ty);+;) => {
        paste::paste! {$(
            #[doc = concat!("invalid ", stringify!($ty:lower))]
            #[derive(Clone, Copy, Debug)]
            pub struct [<Invalid $ty>](pub(crate) $prim);

            #[cfg(feature = "std")]
            impl std::error::Error for [<Invalid $ty>] {}

            impl [<Invalid $ty>] {
                /// Returns the invalid u8.
                #[inline]
                #[must_use]
                pub const fn into_inner(self) -> $prim {
                    self.0
                }
            }

            impl core::fmt::Display for [<Invalid $ty>] {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    write!(f, "{} is not a valid value", self.0)
                }
            }
        )+}
    };
}

into_error! {
    Universe => u8;
    AccountType => u8;
    ChatFlags => u32;
    Instance => u32;
    AccountNumber => u32;
    AccountId => u32;
    AuthServer => u8;
}
