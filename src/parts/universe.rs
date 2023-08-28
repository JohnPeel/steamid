use crate::{error::InvalidValue, macros::forward_impl};

/// Universe part of a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Universe {
    /// Invalid.
    Invalid = 0,
    /// The standard public universe.
    Public = 1,
    /// Beta universe used inside Valve.
    Beta = 2,
    /// Internal universe used inside Valve.
    Internal = 3,
    /// Dev universe used inside Valve.
    Developer = 4,
    /// RC (this doesn't exist in the steam_api documentation)
    Rc = 5,
}

impl Universe {
    /// Convert into a [`u8`].
    #[must_use]
    pub const fn into_u8(self) -> u8 {
        self as u8
    }

    /// Convert from a [`u8`].
    ///
    /// # Errors
    /// Value must be under `6`.
    pub const fn try_from_u8(value: u8) -> Result<Self, InvalidValue<u8>> {
        Ok(match value {
            0 => Self::Invalid,
            1 => Self::Public,
            2 => Self::Beta,
            3 => Self::Internal,
            4 => Self::Developer,
            5 => Self::Rc,
            _ => return Err(InvalidValue::new(value)),
        })
    }
}

forward_impl!(use into_u8; impl Into<u8> for Universe);
forward_impl!(use try_from_u8; impl TryFrom<u8, Error = InvalidValue<u8>> for Universe);
