use crate::macros::forward_impl;

/// Account id part of a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct AccountId(u32);

impl AccountId {
    /// Convert into a [`u32`].
    #[must_use]
    pub const fn into_u32(self) -> u32 {
        self.0
    }

    /// Convert from a [`u32`].
    #[must_use]
    pub const fn from_u32(value: u32) -> Self {
        Self(value)
    }
}

forward_impl!(use into_u32; impl Into<u32> for AccountId);
forward_impl!(use from_u32; impl From<u32> for AccountId);
