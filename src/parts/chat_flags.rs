use crate::{error::InvalidValue, macros::forward_impl};

/// Chat flags part of a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u32)]
pub enum ChatFlags {
    /// Clan based chat
    Clan = 1 << 7,
    /// Lobby based chat
    Lobby = 1 << 6,
    /// Matchmaking lobby based chat
    MatchmakingLobby = 1 << 5,
}

impl ChatFlags {
    /// Convert into a [`u32`].
    #[must_use]
    pub const fn into_u32(self) -> u32 {
        self as u32
    }

    /// Convert from a [`u32`].
    ///
    /// # Errors
    /// Value must be a power of two, between 32 and 128 (both inclusive).
    pub const fn try_from_u32(value: u32) -> Result<Self, InvalidValue<u32>> {
        Ok(match value {
            128 => Self::Clan,
            64 => Self::Lobby,
            32 => Self::MatchmakingLobby,
            _ => return Err(InvalidValue::new(value)),
        })
    }
}

forward_impl!(use into_u32; impl Into<u32> for ChatFlags);
forward_impl!(use try_from_u32; impl TryFrom<u32, Error = InvalidValue<u32>> for ChatFlags);
