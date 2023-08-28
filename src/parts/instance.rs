use crate::{error::InvalidValue, macros::forward_impl};

/// Instance part of a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u32)]
pub enum Instance {
    /// All
    All = 0,
    /// Desktop
    Desktop = 1,
    /// Console
    Console = 2,
    /// Web
    Web = 4,
}

impl Instance {
    /// Convert into a [`u32`].
    #[must_use]
    pub const fn into_u32(self) -> u32 {
        self as u32
    }

    /// Convert from a [`u32`].
    ///
    /// # Errors
    /// Value must be between `0` and `2` (both inclusive), or `4`.
    pub const fn try_from_u32(value: u32) -> Result<Self, InvalidValue<u32>> {
        Ok(match value {
            0 => Self::All,
            1 => Self::Desktop,
            2 => Self::Console,
            4 => Self::Web,
            _ => return Err(InvalidValue::new(value)),
        })
    }
}

forward_impl!(use into_u32; impl Into<u32> for Instance);
forward_impl!(use try_from_u32; impl TryFrom<u32, Error = InvalidValue<u32>> for Instance);
