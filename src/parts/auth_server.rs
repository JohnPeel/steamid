use crate::{error::InvalidValue, macros::forward_impl};

/// Auth server part of a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum AuthServer {
    /// 0
    Zero = 0,
    /// 1
    One = 1,
}

impl AuthServer {
    /// Convert into a [`u8`].
    #[must_use]
    pub const fn into_u8(self) -> u8 {
        self as u8
    }

    /// Convert from a [`u8`].
    ///
    /// # Errors
    /// Value must be `0` or `1`.
    pub const fn try_from_u8(value: u8) -> Result<Self, InvalidValue<u8>> {
        Ok(match value {
            0 => Self::Zero,
            1 => Self::One,
            _ => return Err(InvalidValue::new(value)),
        })
    }
}

forward_impl!(use into_u8; impl Into<u8> for AuthServer);
forward_impl!(use try_from_u8; impl TryFrom<u8, Error = InvalidValue<u8>> for AuthServer);
