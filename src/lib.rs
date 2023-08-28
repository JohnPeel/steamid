//! # Steam ID type and accessories
//!
//! This project provides the `SteamId` type with conversion methods to convert between different Steam Id formats.
//!
//! Hosted on [GitHub](https://github.com/JohnPeel/steamid-rs).
//!
//! ## Examples and Usage
//!
//! ### Initialize from steam64id
//! ```rust
//! # use steamid::{SteamId, Error};
//! # fn main() -> Result<(), Error> {
//! let steamid = SteamId::new(76561198181797231)?;
//! #   Ok(())
//! # }
//! ```
//!
//! ### Parse a steam2id
//! ```rust
//! # use steamid::{SteamId, AccountType, Instance, Error};
//! # fn main() -> Result<(), Error> {
//! let steamid = SteamId::parse_steam2id("STEAM_0:0:12345", AccountType::Individual, Instance::Desktop)?;
//! # Ok(())
//! # }
//! ```
//!
//! ### Parse a steam3id
//! ```rust
//! # use steamid::{SteamId, Instance, Error};
//! # fn main() -> Result<(), Error> {
//! let steamid = SteamId::parse_steam3id("[U:1:12345]", Instance::Desktop)?;
//! # Ok(())
//! # }
//! ```
//!
//! ### Convert steam64id to steam2id
//! ```rust
//! # use steamid::{SteamId, Error};
//! # fn main() -> Result<(), Error> {
//! let steamid = SteamId::new(76561198181797231)?;
//! let steam2id = steamid.steam2id();
//! # Ok(())
//! # }
//! ```
//!
//! ### Convert steam64id to steam3id
//! ```rust
//! # use steamid::{SteamId, Error};
//! # fn main() -> Result<(), Error> {
//! let steamid = SteamId::new(76561198181797231)?;
//! let steam3id = steamid.steam3id();
//! # Ok(())
//! # }
//! ```
//!
//! ### Convert steam64id to Community Link
//! ```rust
//! # use steamid::{SteamId, Error};
//! # fn main() -> Result<(), Error> {
//! let steamid = SteamId::new(76561198181797231)?;
//! let community_link = steamid.community_link();
//! # Ok(())
//! # }
//! ```
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(
    missing_docs,
    rustdoc::missing_crate_level_docs,
    rustdoc::private_doc_tests,
    clippy::pedantic
)]
#![deny(unsafe_code)]
// TODO: Remove when this when the lint supports inner attribute or num_enum is updated to use a normal attribute.
#![allow(non_upper_case_globals)]

#[cfg(not(feature = "std"))]
extern crate alloc;

/// Error types.
pub mod error;
mod raw;

#[cfg(not(feature = "std"))]
use alloc::{format, string::String};

use error::{
    InvalidAccountNumber, InvalidAccountType, InvalidAuthServer, InvalidChatFlags, InvalidInstance,
    InvalidUniverse,
};
use from_enum::From;

pub use self::error::{Error, Result};
pub use self::raw::RawSteamId;

/// Representation of a Steam id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct SteamId(RawSteamId);

macro_rules! into_repr {
    ($ty:ty => $prim:ty) => {
        paste::paste! {
            impl $ty {
                #[doc = concat!("Converts `", stringify!($ty), "` into a `", stringify!($prim), "`.")]
                #[inline]
                #[must_use]
                pub const fn [<into_ $prim>](self) -> $prim {
                    self as $prim
                }
            }

            impl From<$ty> for $prim {
                #[inline]
                fn from(value: $ty) -> $prim {
                    value.[<into_ $prim>]()
                }
            }

            impl TryFrom<$prim> for $ty {
                type Error = [<Invalid $ty>];

                #[inline]
                fn try_from(value: $prim) -> Result<Self, Self::Error> {
                    Self::[<try_from_ $prim>](value)
                }
            }
        }
    };
}

/// Representation of the universe a `SteamId` is associated with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
into_repr!(Universe => u8);

impl Universe {
    /// Converts the `u8` into a `Universe`.
    ///
    /// # Errors
    /// `u8` outside of the range `0..=5` are invalid.
    #[inline]
    pub const fn try_from_u8(value: u8) -> Result<Self, InvalidUniverse> {
        Ok(match value {
            0 => Self::Invalid,
            1 => Self::Public,
            2 => Self::Beta,
            3 => Self::Internal,
            4 => Self::Developer,
            5 => Self::Rc,
            _ => return Err(InvalidUniverse(value)),
        })
    }
}

/// Representation of an account type for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
    /// The format of this type is still unknown, and they will not work with this library.
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
into_repr!(AccountType => u8);

impl AccountType {
    /// Returns the character representation of the `AccountType` (if possible).
    ///
    /// # Errors
    /// `AccountType` without a character representation will result in an error.
    pub const fn try_into_char(&self) -> Result<char, Error> {
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
            Self::ConsoleUser => return Err(Error::NoCharacterRepresentation(*self)),
            Self::AnonUser => 'a',
        })
    }

    /// Construct an `AccountType` from the character representation (if possible).
    ///
    /// # Errors
    /// Invalid character representations will result in an error.
    pub const fn try_from_char(value: char) -> Result<Self, Error> {
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
            _ => return Err(Error::InvalidCharacterRepresentation(value)),
        })
    }

    /// Converts the `u8` into a `AccountType`.
    ///
    /// # Errors
    /// `u8` outside of the range `0..=10` are invalid.
    #[inline]
    pub const fn try_from_u8(value: u8) -> Result<Self, InvalidAccountType> {
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
            _ => return Err(InvalidAccountType(value)),
        })
    }
}

impl TryFrom<char> for AccountType {
    type Error = Error;

    #[inline]
    fn try_from(value: char) -> Result<Self, Self::Error> {
        Self::try_from_char(value)
    }
}

impl TryFrom<AccountType> for char {
    type Error = Error;

    #[inline]
    fn try_from(value: AccountType) -> Result<Self> {
        value.try_into_char()
    }
}

/// Representation of chat flags for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(u32)]
pub enum ChatFlags {
    /// Clan based chat
    Clan = 1 << 7,
    /// Lobby based chat
    Lobby = 1 << 6,
    /// Matchmaking lobby based chat
    MatchmakingLobby = 1 << 5,
}
into_repr!(ChatFlags => u32);

impl ChatFlags {
    /// Construct an `ChatFlags` given a `u32`.
    ///
    /// # Errors
    /// `value` must be valid chat flags.
    #[inline]
    pub const fn try_from_u32(value: u32) -> Result<Self, InvalidChatFlags> {
        Ok(match value {
            128 => Self::Clan,
            64 => Self::Lobby,
            32 => Self::MatchmakingLobby,
            _ => return Err(InvalidChatFlags(value)),
        })
    }
}

/// Representation of an instance for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
into_repr!(Instance => u32);

impl Instance {
    /// Construct an `Instance` given a `u32`.
    ///
    /// # Errors
    /// `value` must be a valid instance: `0..3 | 4`.
    #[inline]
    pub const fn try_from_u32(value: u32) -> Result<Self, InvalidInstance> {
        Ok(match value {
            0 => Self::All,
            1 => Self::Desktop,
            2 => Self::Console,
            4 => Self::Web,
            _ => return Err(InvalidInstance(value)),
        })
    }
}

/// Representation of an account number for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct AccountNumber(u32);

impl AccountNumber {
    /// Returns the inner `u32`.
    #[inline]
    #[must_use]
    pub const fn into_inner(self) -> u32 {
        self.0
    }

    /// Converts an `AccountNumber` into a `u32`.
    #[inline]
    #[must_use]
    pub const fn into_u32(self) -> u32 {
        self.0
    }

    /// Construct an `AccountNumber` given a `u32`.
    ///
    /// # Errors
    /// Account numbers are restricted to below `0x7FFF_FFFF`.
    #[inline]
    pub const fn try_from_u32(value: u32) -> Result<Self, InvalidAccountNumber> {
        if value > 0x7FFF_FFFF {
            return Err(InvalidAccountNumber(value));
        }
        Ok(Self(value))
    }
}

/// Representation of an account id for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct AccountId(u32);

impl AccountId {
    /// Returns the inner `u32`.
    #[inline]
    #[must_use]
    pub const fn into_inner(self) -> u32 {
        self.0
    }

    /// Converts an `AccountId` into a `u32`.
    #[inline]
    #[must_use]
    pub const fn into_u32(self) -> u32 {
        self.0
    }

    /// Construct an `AccountId` given a `u32`.
    #[inline]
    #[must_use]
    pub const fn from_u32(value: u32) -> Self {
        Self(value)
    }
}

/// Which auth server is used for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(u8)]
pub enum AuthServer {
    /// 0
    Zero = 0,
    /// 1
    One = 1,
}
into_repr!(AuthServer => u8);

impl AuthServer {
    /// Construct an `AuthServer` given a `u8`.
    ///
    /// # Errors
    /// Only `0` and `1` are valid values for `AuthServer`.
    #[inline]
    pub const fn try_from_u8(value: u8) -> Result<Self, InvalidAuthServer> {
        Ok(match value {
            0 => Self::Zero,
            1 => Self::One,
            _ => return Err(InvalidAuthServer(value)),
        })
    }
}

impl From<SteamId> for u64 {
    #[inline]
    fn from(steam_id: SteamId) -> Self {
        steam_id.into_inner().into_inner()
    }
}

impl TryFrom<u64> for SteamId {
    type Error = Error;

    #[inline]
    fn try_from(steam_id: u64) -> Result<Self, Self::Error> {
        Self::new(steam_id)
    }
}

impl SteamId {
    /// Contructs a new `SteamId` from a raw u64.
    ///
    /// # NOTE
    /// If you use this, you should be using the `try_` version of each method on [`SteamId`].
    ///
    /// If you use another library that accepts a [`SteamId`], be forwarned that using the
    /// non-`try_` versions will panic with invalid [`SteamId`] constructed with this method.
    #[inline]
    #[must_use]
    pub const fn new_unchecked(steam_id: u64) -> Self {
        SteamId(RawSteamId::new(steam_id))
    }

    /// Constructs a new `SteamId` from a steam64id.
    ///
    /// # Errors
    /// This method will return an error if the steam64id is invalid.
    pub fn new(steam_id: u64) -> Result<Self> {
        let steam_id = Self::new_unchecked(steam_id);
        steam_id.try_universe()?;
        steam_id.try_account_type()?;
        steam_id.try_instance()?;
        steam_id.try_account_number()?;
        Ok(steam_id)
    }

    /// Returns the raw representation of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn into_inner(&self) -> RawSteamId {
        self.0
    }

    /// Returns the raw universe of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn raw_universe(&self) -> u8 {
        self.into_inner().universe()
    }

    /// Returns the `Universe` of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the universe is invalid.
    pub const fn try_universe(&self) -> Result<Universe> {
        match Universe::try_from_u8(self.raw_universe()) {
            Ok(universe) => Ok(universe),
            Err(error) => Err(Error::InvalidUniverse(error)),
        }
    }

    /// Returns the `Universe` of the `SteamId`.
    ///
    /// # Panics
    /// This method panics if the universe is invalid.
    #[must_use]
    pub fn universe(&self) -> Universe {
        self.try_universe().unwrap()
    }

    /// Sets the `Universe` of the `SteamId`.
    #[inline]
    pub fn set_universe(&mut self, universe: Universe) {
        *self = Self(self.into_inner().with_universe(u8::from(universe)));
    }

    /// Returns the raw account type of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn raw_account_type(&self) -> u8 {
        self.into_inner().account_type()
    }

    /// Returns the account type of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the account type is invalid.
    pub const fn try_account_type(&self) -> Result<AccountType> {
        match AccountType::try_from_u8(self.raw_account_type()) {
            Ok(universe) => Ok(universe),
            Err(error) => Err(Error::InvalidAccountType(error)),
        }
    }

    /// Returns the account type of the `SteamId`.
    ///
    /// # Panics
    /// This method panics if the account type is invalid.
    #[must_use]
    pub fn account_type(&self) -> AccountType {
        self.try_account_type().unwrap()
    }

    /// Sets the account type of the `SteamId`.
    #[inline]
    pub fn set_account_type(&mut self, account_type: AccountType) {
        if account_type != AccountType::Chat {
            self.reset_chat_flags();
        }

        *self = Self(self.into_inner().with_account_type(u8::from(account_type)));
    }

    /// Returns the raw chat flags of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn raw_chat_flags(&self) -> u32 {
        self.into_inner().chat_flags()
    }

    /// Returns the chat flags of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the chat flags are invalid.
    pub const fn try_chat_flags(&self) -> Result<Option<ChatFlags>> {
        let chat_flags = self.raw_chat_flags();
        if chat_flags == 0 {
            return Ok(None);
        }

        match ChatFlags::try_from_u32(chat_flags) {
            Ok(chat_flags) => Ok(Some(chat_flags)),
            Err(error) => Err(Error::InvalidChatFlags(error)),
        }
    }

    /// Returns the chat flags of the `SteamId`.
    ///
    /// # Panics
    /// This method panics if the chat flags are invalid.
    #[must_use]
    pub fn chat_flags(&self) -> Option<ChatFlags> {
        self.try_chat_flags().unwrap()
    }

    /// Reset the chat flags of the `SteamId`.
    pub fn reset_chat_flags(&mut self) {
        *self = Self(self.0.with_chat_flags(0));
    }

    /// Sets the chat flags of the `SteamId`.
    #[inline]
    pub fn set_chat_flags(&mut self, chat_flags: ChatFlags) {
        self.reset_chat_flags();
        self.set_account_type(AccountType::Chat);
        *self = Self(self.0.with_chat_flags(u32::from(chat_flags)));
    }

    /// Returns the raw instance of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn raw_instance(&self) -> u32 {
        self.into_inner().instance()
    }

    /// Returns the `Instance` of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the instance is invalid.
    pub const fn try_instance(&self) -> Result<Instance> {
        match Instance::try_from_u32(self.raw_instance()) {
            Ok(instance) => Ok(instance),
            Err(error) => Err(Error::InvalidInstance(error)),
        }
    }

    /// Returns the `Instance` of the `SteamId`.
    ///
    /// # Panics
    /// This method panics if the instance is invalid.
    #[inline]
    #[must_use]
    pub fn instance(&self) -> Instance {
        self.try_instance().unwrap()
    }

    /// Sets the instance of the `SteamId`.
    #[inline]
    pub fn set_instance(&mut self, instance: Instance) {
        *self = Self(self.into_inner().with_instance(u32::from(instance)));
    }

    /// Returns the raw account number of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn raw_account_number(&self) -> u32 {
        self.into_inner().account_number()
    }

    /// Returns the `AccountNumber` of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the account number is invalid.
    #[inline]
    pub const fn try_account_number(&self) -> Result<AccountNumber> {
        match AccountNumber::try_from_u32(self.raw_account_number()) {
            Ok(account_number) => Ok(account_number),
            Err(error) => Err(Error::InvalidAccountNumber(error)),
        }
    }

    /// Returns the `AccountNumber` of the `SteamId`.
    ///
    /// # Panics
    /// This method panics if the account number is invalid.
    #[must_use]
    pub fn account_number(&self) -> AccountNumber {
        self.try_account_number().unwrap()
    }

    /// Sets the `AccountNumber` of the `SteamId`.
    #[inline]
    pub fn set_account_number(&mut self, account_number: AccountNumber) {
        *self = Self(
            self.into_inner()
                .with_account_number(account_number.into_u32()),
        );
    }

    /// Returns the raw account id of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn raw_account_id(&self) -> u32 {
        self.into_inner().account_id()
    }

    /// Returns the `AccountId` of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn account_id(&self) -> AccountId {
        AccountId(self.raw_account_id())
    }

    /// Sets the `AccountId` of the `SteamId`.
    #[inline]
    pub fn set_account_id(&mut self, account_id: AccountId) {
        *self = Self(self.into_inner().with_account_id(account_id.into_u32()));
    }

    /// Returns the raw auth server portion of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn raw_auth_server(&self) -> u8 {
        self.into_inner().auth_server()
    }

    /// Returns the `AuthServer` of the `SteamId`.
    ///
    /// # Panics
    /// This method will not panic.
    #[must_use]
    pub fn auth_server(&self) -> AuthServer {
        // SAFETY: The unwrap is possible because AuthServer variants cover every case. (0 and 1)
        AuthServer::try_from(self.raw_auth_server()).unwrap()
    }

    /// Sets the `AuthServer` of the `SteamId`.
    #[inline]
    pub fn set_auth_server(&mut self, auth_server: AuthServer) {
        *self = Self(self.into_inner().with_auth_server(u8::from(auth_server)));
    }

    /// Construct a static account key from the static parts of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn static_account_key(&self) -> u64 {
        ((self.raw_universe() as u64) << 56)
            | ((self.raw_account_type() as u64) << 52)
            | (self.raw_account_id() as u64)
    }

    /// Returns the steam2id representation of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the universe or account number are invalid.
    pub fn try_steam2id(&self) -> Result<String> {
        Ok(format!(
            "STEAM_{}:{}:{}",
            self.try_universe()?.into_u8(),
            self.auth_server().into_u8(),
            self.try_account_number()?.into_u32(),
        ))
    }

    /// Returns the steam2id representation of the `SteamId`.
    ///
    /// # Panics
    /// This method panics if the universe or account number are invalid.
    #[must_use]
    pub fn steam2id(&self) -> String {
        self.try_steam2id().unwrap()
    }

    /// Returns the steam3id representation of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the account type or universe are invalid.
    pub fn try_steam3id(&self) -> Result<String> {
        let account_type = self.try_account_type()?;
        let instance = matches!(
            account_type,
            AccountType::AnonGameServer | AccountType::Multiseat
        )
        .then(|| self.try_instance())
        .transpose()?
        .map(|instance| format!(":{}", u32::from(instance)));

        let account_type = match account_type {
            AccountType::Chat => match self.try_chat_flags()? {
                Some(ChatFlags::Clan) => 'c',
                Some(ChatFlags::Lobby) => 'L',
                Some(ChatFlags::MatchmakingLobby) => {
                    return Err(Error::NoCharacterRepresentation(AccountType::Chat))
                }
                None => char::try_from(AccountType::Chat)?,
            },
            value => char::try_from(value)?,
        };

        Ok(format!(
            "[{}:{}:{}{}]",
            account_type,
            self.try_universe()?.into_u8(),
            self.account_id().into_u32(),
            instance.as_deref().unwrap_or_default()
        ))
    }

    /// Returns the steam3id representation of the `SteamId`.
    ///
    /// # Panics
    /// This method panics if the account type or universe are invalid.
    #[must_use]
    pub fn steam3id(&self) -> String {
        self.try_steam3id().unwrap()
    }

    /// Returns a generalized version of this `SteamId`.
    ///
    /// This method keeps the account number that same, but sets other parameters to their defaults.
    #[must_use]
    pub fn generalize(&self) -> Self {
        let mut steamid = *self;
        steamid.reset_chat_flags();
        steamid.set_universe(Universe::Public);
        steamid.set_account_type(AccountType::Individual);
        steamid.set_instance(Instance::Desktop);
        steamid
    }

    /// Returns the community link for the `SteamId`.
    #[must_use]
    pub fn community_link(&self) -> String {
        format!(
            "https://steamcommunity.com/profiles/{}",
            u64::from(self.generalize())
        )
    }

    /// Parse steam2id into a `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the steam2id is invalid.
    pub fn parse_steam2id<S: AsRef<str>>(
        value: S,
        account_type: impl Into<Option<AccountType>>,
        instance: impl Into<Option<Instance>>,
    ) -> Result<Self> {
        let value = value.as_ref();
        let account_type = account_type.into().unwrap_or(AccountType::Individual);
        let instance = instance.into().unwrap_or(Instance::Desktop);

        if !value.starts_with("STEAM_") {
            Err(Error::ParseError("does not start with `STEAM_`"))?;
        }

        let mut parts = value[6..].split(':');

        let universe = parts
            .next()
            .ok_or(Error::ParseError("missing universe"))
            .and_then(|v| {
                v.parse::<u8>()
                    .map_err(|_| Error::ParseError("universe is not an integer"))
            })
            .and_then(|v| Ok(Universe::try_from_u8(v)?))?;
        let auth_server = parts
            .next()
            .ok_or(Error::ParseError("missing auth server"))
            .and_then(|v| {
                v.parse::<u8>()
                    .map_err(|_| Error::ParseError("auth server is not an integer"))
            })
            .and_then(|v| Ok(AuthServer::try_from_u8(v)?))?;
        let account_number = parts
            .next()
            .ok_or(Error::ParseError("missing account number"))
            .and_then(|v| {
                v.parse::<u32>()
                    .map_err(|_| Error::ParseError("account number is not an integer"))
            })
            .and_then(|v| Ok(AccountNumber::try_from_u32(v)?))?;

        let raw_sid = RawSteamId::new(0)
            .with_universe(universe.into_u8())
            .with_account_type(account_type.into_u8())
            .with_instance(instance.into_u32())
            .with_account_number(account_number.into_u32())
            .with_auth_server(auth_server.into_u8());
        Ok(SteamId(raw_sid))
    }

    /// Parse steam3id into a `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the steam3id is invalid.
    pub fn parse_steam3id<S: AsRef<str>>(
        value: S,
        default_instance: impl Into<Option<Instance>>,
    ) -> Result<Self> {
        let mut value = value.as_ref();
        let default_instance = default_instance.into().unwrap_or(Instance::All);

        if value.starts_with('[') && value.ends_with(']') {
            value = &value[1..value.len() - 1];
        }

        let mut parts = value.split(':');

        let account_type = parts
            .next()
            .filter(|v| v.len() == 1)
            .ok_or(Error::ParseError("missing account type"))
            .map(str::chars)?
            .next()
            .ok_or(Error::ParseError("account type should be a character"))?;
        let chat_flags = match account_type {
            'c' => Some(ChatFlags::Clan),
            'L' => Some(ChatFlags::Lobby),
            _ => None,
        };
        let account_type = AccountType::try_from(account_type)?;
        let universe = parts
            .next()
            .ok_or(Error::ParseError("missing universe"))
            .and_then(|v| {
                v.parse::<u8>()
                    .map_err(|_| Error::ParseError("universe is not an integer"))
            })
            .and_then(|v| Ok(Universe::try_from(v)?))?;
        let account_id = parts
            .next()
            .ok_or(Error::ParseError("missing account id"))
            .and_then(|v| {
                v.parse::<u32>()
                    .map_err(|_| Error::ParseError("account id is not an integer"))
            })
            .map(AccountId::from_u32)?;

        let instance = match account_type {
            AccountType::Chat | AccountType::Clan => Instance::All,
            AccountType::Individual => Instance::Desktop,
            AccountType::AnonGameServer | AccountType::Multiseat => parts
                .next()
                .ok_or(Error::ParseError("missing instance"))
                .and_then(|v| {
                    v.parse::<u32>()
                        .map_err(|_| Error::ParseError("instance is not an integer"))
                })
                .map(Instance::try_from)??,
            _ => default_instance,
        };

        let raw_sid = RawSteamId::new(0)
            .with_universe(universe.into_u8())
            .with_account_type(account_type.into_u8())
            .with_instance(instance.into_u32())
            .with_chat_flags(chat_flags.map_or(0, ChatFlags::into_u32))
            .with_account_id(account_id.into_u32());
        Ok(SteamId(raw_sid))
    }
}

#[cfg(test)]
mod tests {
    use crate::{AccountType, ChatFlags, Instance, SteamId, Universe};

    #[test]
    fn steamid_to_others() {
        let steamid = SteamId::new(76_561_197_999_189_721).unwrap();
        assert_eq!(steamid.steam2id(), "STEAM_1:1:19461996");
        assert_eq!(steamid.steam3id(), "[U:1:38923993]");
    }

    #[test]
    fn steamid_from_steam2id() {
        let steamid = SteamId::parse_steam2id("STEAM_1:1:19461996", None, None).unwrap();
        assert_eq!(steamid, SteamId::new_unchecked(76_561_197_999_189_721));
    }

    #[test]
    fn steamid_from_steam3id() {
        let steamid = SteamId::parse_steam3id("[U:1:38923993]", None).unwrap();
        assert_eq!(steamid, SteamId::new_unchecked(76_561_197_999_189_721));
    }

    #[test]
    fn steamid_universe_change() {
        let mut steamid = SteamId::new(76_561_197_999_189_721).unwrap();
        assert_eq!(steamid.steam2id(), "STEAM_1:1:19461996");
        assert_eq!(steamid.universe(), Universe::Public);
        steamid.set_universe(Universe::Invalid);
        assert_eq!(steamid.universe(), Universe::Invalid);
        assert_eq!(steamid.steam2id(), "STEAM_0:1:19461996");
    }

    #[test]
    fn steamid_community_link() {
        let steamid = SteamId::parse_steam2id("STEAM_0:1:19461996", None, None).unwrap();
        assert_eq!(
            steamid.community_link(),
            "https://steamcommunity.com/profiles/76561197999189721"
        );
    }

    #[test]
    fn steamid_validation() {
        SteamId::new(76_561_197_982_148_920).unwrap();
        SteamId::new(76_561_197_999_189_721).unwrap();
        SteamId::new(76_561_197_960_287_930).unwrap();
    }

    #[test]
    fn steamid_chat_flags() {
        let steamid = SteamId::parse_steam3id("[L:1:38923993]", None).unwrap();

        assert_eq!(steamid.account_type(), AccountType::Chat);
        assert_eq!(steamid.chat_flags(), Some(ChatFlags::Lobby));
    }

    #[test]
    fn steamid_multiseat_steam3id() {
        let steamid = SteamId::parse_steam3id("[M:1:38923993:4]", None).unwrap();

        assert_eq!(steamid.account_type(), AccountType::Multiseat);
        // Since this is multiseat and has instance in the steam3id, the instance passed to parse_steam3id is ignored.
        assert_eq!(steamid.instance(), Instance::Web);

        assert_eq!(steamid.steam3id(), "[M:1:38923993:4]");
    }
}
