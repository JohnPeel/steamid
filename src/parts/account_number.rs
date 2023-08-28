use crate::{error::InvalidValue, macros::forward_impl};

/// Account number part of a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct AccountNumber(u32);

impl AccountNumber {
    /// Convert into a [`u32`].
    #[must_use]
    pub const fn into_u32(self) -> u32 {
        self.0
    }

    /// Convert from a [`u32`].
    ///
    /// # Errors
    /// Values over `0x7FFF_FFFF` are invalid.
    pub const fn try_from_u32(value: u32) -> Result<Self, InvalidValue<u32>> {
        if value > 0x7FFF_FFFF {
            return Err(InvalidValue::new(value));
        }
        Ok(Self(value))
    }
}

forward_impl!(use into_u32; impl Into<u32> for AccountNumber);
forward_impl!(use try_from_u32; impl TryFrom<u32, Error = InvalidValue<u32>> for AccountNumber);
