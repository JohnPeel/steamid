use crate::{error::InvalidValue, macros::forward_impl};

/// Account type part of a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum AccountType {
    /// Used for invalid Steam IDs.
    Invalid = 0,
    /// Regular user account.
    Individual = 1,
    /// Multiseat (e.g. cybercafe) account.
    Multiseat = 2,
    /// Persistent (not anonymous) game server account.
    GameServer = 3,
    /// Anonymous game server account.
    ///
    /// The format of this type is still unknown, and it will not work with this library.
    AnonGameServer = 4,
    /// Pending.
    Pending = 5,
    /// Valve internal content server account.
    ContentServer = 6,
    /// Steam Group (clan).
    Clan = 7,
    /// Steam group chat or lobby.
    Chat = 8,
    /// Fake Steam ID for local PSN account on PS3 or Live account on 360, etc.
    ConsoleUser = 9,
    /// Anonymous user account. (Used to create an account or reset a password)
    AnonUser = 10,
}

impl AccountType {
    /// Convert into a [`u8`].
    #[must_use]
    pub const fn into_u8(self) -> u8 {
        self as u8
    }

    /// Convert from a [`u8`].
    ///
    /// # Errors
    /// Values over `10` are invalid.
    pub const fn try_from_u8(value: u8) -> Result<Self, InvalidValue<u8>> {
        Ok(match value {
            0 => Self::Invalid,
            1 => Self::Individual,
            2 => Self::Multiseat,
            3 => Self::GameServer,
            4 => Self::AnonGameServer,
            5 => Self::Pending,
            6 => Self::ContentServer,
            7 => Self::Clan,
            8 => Self::Chat,
            9 => Self::ConsoleUser,
            10 => Self::AnonUser,
            _ => return Err(InvalidValue::new(value)),
        })
    }

    /// Convert into a [`char`].
    ///
    /// # Errors
    /// `ConsoleUser` does not have a character representation.
    pub const fn try_into_char(self) -> Result<char, InvalidValue<Self>> {
        Ok(match self {
            Self::Invalid => 'I',
            Self::Individual => 'U',
            Self::Multiseat => 'M',
            Self::GameServer => 'G',
            Self::AnonGameServer => 'A',
            Self::Pending => 'P',
            Self::ContentServer => 'C',
            Self::Clan => 'g',
            Self::Chat => 'T',
            Self::ConsoleUser => return Err(InvalidValue::new(self)),
            Self::AnonUser => 'a',
        })
    }

    /// Convert from a [`char`].
    ///
    /// # Errors
    /// Value must be a character within `IUMGAPCgTLca`.
    pub const fn try_from_char(value: char) -> Result<Self, InvalidValue<char>> {
        Ok(match value {
            'I' => Self::Invalid,
            'U' => Self::Individual,
            'M' => Self::Multiseat,
            'G' => Self::GameServer,
            'A' => Self::AnonGameServer,
            'P' => Self::Pending,
            'C' => Self::ContentServer,
            'g' => Self::Clan,
            'T' | 'L' | 'c' => Self::Chat,
            'a' => Self::AnonUser,
            _ => return Err(InvalidValue::new(value)),
        })
    }
}

forward_impl!(use into_u8; impl Into<u8> for AccountType);
forward_impl!(use try_from_u8; impl TryFrom<u8, Error = InvalidValue<u8>> for AccountType);

forward_impl!(use try_into_char; impl TryInto<char, Error = InvalidValue<AccountType>> for AccountType);
forward_impl!(use try_from_char; impl TryFrom<char, Error = InvalidValue<char>> for AccountType);
