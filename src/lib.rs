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

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::{format, string::String};

use core::convert::TryInto;

use derive_more::Into;
use displaydoc::Display;
use from_enum::From;
use num_enum::{IntoPrimitive, TryFromPrimitive, TryFromPrimitiveError};

/// Representation of a Steam id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct SteamId(u64);

/// Representation of the universe a `SteamId` is associated with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum Universe {
    /// Individual or Unspecified
    Individual = 0,
    /// Public
    Public = 1,
    /// Beta
    Beta = 2,
    /// Internal
    Internal = 3,
    /// Developer
    Developer = 4,
    /// RC
    Rc = 5,
}

/// Representation of an account type for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum AccountType {
    /// Invalid
    Invalid = 0,
    /// Individual
    Individual = 1,
    /// Multiseat
    Multiseat = 2,
    /// Game Server
    GameServer = 3,
    /// Anon Game Server
    AnonGameServer = 4,
    /// Pending
    Pending = 5,
    /// Content Server
    ContentServer = 6,
    /// Clan
    Clan = 7,
    /// Chat
    Chat = 8,
    /// P2P SuperSeeder
    P2pSuperSeeder = 9,
    /// Anon User
    AnonUser = 10,
}

// TODO: Support Chat flags.
/// Representation of an instance for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(IntoPrimitive, TryFromPrimitive)]
#[repr(u32)]
pub enum Instance {
    /// All
    All = 0,
    /// Desktop
    Desktop = 1,
    /// Console
    Console = 2,
    /// Web
    Web = 3,
}

/// Representation of an account number for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Into)]
pub struct AccountNumber(u32);

/// Representation of an account id for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Into, derive_more::From)]
pub struct AccountId(u32);

/// Representation of the parity bit for a `SteamId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum ParityBit {
    /// The parity is even.
    Even = 0,
    /// The parity is odd.
    Odd = 1,
}

/// Error type for crate.
#[derive(Debug, Display, From)]
pub enum Error {
    /// invalid universe: {0}
    InvalidUniverse(#[from] TryFromPrimitiveError<Universe>),
    /// invalid account type: {0}
    InvalidAccountType(#[from] TryFromPrimitiveError<AccountType>),
    /// invalid instance: {0}
    InvalidInstance(#[from] TryFromPrimitiveError<Instance>),
    /// invalid account number: {0}
    InvalidAccountNumber(u32),
    /// invalid parity bit: {0}
    InvalidParityBit(#[from] TryFromPrimitiveError<ParityBit>),

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
type Result<T, E = Error> = core::result::Result<T, E>;

impl TryFrom<char> for AccountType {
    type Error = Error;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        use AccountType::{
            AnonGameServer, AnonUser, Chat, Clan, ContentServer, GameServer, Individual, Invalid,
            Multiseat, Pending,
        };
        Ok(match value {
            'I' => Invalid,
            'U' => Individual,
            'M' => Multiseat,
            'G' => GameServer,
            'A' => AnonGameServer,
            'P' => Pending,
            'C' => ContentServer,
            'g' => Clan,
            'T' | 'L' | 'c' => Chat,
            'a' => AnonUser,
            _ => Err(Error::InvalidCharacterRepresentation(value))?,
        })
    }
}

impl TryFrom<AccountType> for char {
    type Error = Error;

    fn try_from(value: AccountType) -> Result<Self> {
        use AccountType::{
            AnonGameServer, AnonUser, Chat, Clan, ContentServer, GameServer, Individual, Invalid,
            Multiseat, P2pSuperSeeder, Pending,
        };

        Ok(match value {
            Invalid => 'I',
            Individual => 'U',
            Multiseat => 'M',
            GameServer => 'G',
            AnonGameServer => 'A',
            Pending => 'P',
            ContentServer => 'C',
            Clan => 'g',
            Chat => 'T',
            P2pSuperSeeder => Err(Error::NoCharacterRepresentation(value))?,
            AnonUser => 'a',
        })
    }
}

impl TryFrom<u32> for AccountNumber {
    type Error = Error;

    fn try_from(value: u32) -> Result<Self> {
        if value > 0x7FFF_FFFF || value % 2 != 0 {
            Err(Error::InvalidAccountNumber(value))?;
        }
        Ok(Self(value))
    }
}

impl From<SteamId> for u64 {
    #[inline]
    fn from(steam_id: SteamId) -> Self {
        steam_id.0
    }
}

impl TryFrom<u64> for SteamId {
    type Error = Error;

    #[inline]
    fn try_from(steam_id: u64) -> Result<Self, Self::Error> {
        let steam_id = Self(steam_id);
        steam_id.try_universe()?;
        steam_id.try_account_type()?;
        steam_id.try_instance()?;
        steam_id.try_account_number()?;
        Ok(steam_id)
    }
}

impl SteamId {
    const UNIVERSE_MASK: u64 = 0xFF;
    const UNIVERSE_SHIFT: u64 = 56;
    const ACCOUNT_TYPE_MASK: u64 = 0xF;
    const ACCOUNT_TYPE_SHIFT: u64 = 52;
    const INSTANCE_MASK: u64 = 0xF_FFFF;
    const INSTANCE_SHIFT: u64 = 32;
    const ACCOUNT_NUMBER_MASK: u64 = 0xFFFF_FFFF;
    const ACCOUNT_NUMBER_SHIFT: u64 = 1;
    const ACCOUNT_ID_MASK: u64 = 0xFFFF_FFFF;
    const ACCOUNT_ID_SHIFT: u64 = 0;
    const PARITY_BIT_MASK: u64 = 0x1;
    const PARITY_BIT_SHIFT: u64 = 0;

    /// Constructs a new `SteamId` from a steam64id.
    ///
    /// # Errors
    /// This method will return an error if the steam64id is invalid.
    pub fn new(steam_id: u64) -> Result<Self> {
        steam_id.try_into()
    }

    /// Returns the `Universe` of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the universe is invalid.
    pub fn try_universe(&self) -> Result<Universe> {
        Ok(Universe::try_from(
            ((self.0 >> Self::UNIVERSE_SHIFT) & Self::UNIVERSE_MASK) as u8,
        )?)
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
    pub fn set_universe(&mut self, universe: Universe) {
        self.0 = (self.0 & !(Self::UNIVERSE_MASK << Self::UNIVERSE_SHIFT))
            | ((u64::from(u8::from(universe)) & Self::UNIVERSE_MASK) << Self::UNIVERSE_SHIFT);
    }

    /// Returns the account type of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the account type is invalid.
    pub fn try_account_type(&self) -> Result<AccountType> {
        Ok(AccountType::try_from(
            ((self.0 >> Self::ACCOUNT_TYPE_SHIFT) & Self::ACCOUNT_TYPE_MASK) as u8,
        )?)
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
    pub fn set_account_type(&mut self, account_type: AccountType) {
        self.0 = (self.0 & !(Self::ACCOUNT_TYPE_MASK << Self::ACCOUNT_TYPE_SHIFT))
            | ((u64::from(u8::from(account_type)) & Self::ACCOUNT_TYPE_MASK)
                << Self::ACCOUNT_TYPE_SHIFT);
    }

    /// Returns the instance of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the instance is invalid.
    pub fn try_instance(&self) -> Result<Instance> {
        Ok(Instance::try_from(
            ((self.0 >> Self::INSTANCE_SHIFT) & Self::INSTANCE_MASK) as u32,
        )?)
    }

    /// Returns the instance of the `SteamId`.
    ///
    /// # Panics
    /// This method panics if the instance is invalid.
    #[must_use]
    pub fn instance(&self) -> Instance {
        self.try_instance().unwrap()
    }

    /// Sets the instance of the `SteamId`.
    pub fn set_instance(&mut self, instance: Instance) {
        self.0 = (self.0 & !(Self::INSTANCE_MASK << Self::INSTANCE_SHIFT))
            | ((u64::from(u32::from(instance)) & Self::INSTANCE_MASK) << Self::INSTANCE_SHIFT);
    }

    /// Returns the `AccountNumber` of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the account number is invalid.
    pub fn try_account_number(&self) -> Result<AccountNumber> {
        AccountNumber::try_from(
            ((self.0 & Self::ACCOUNT_NUMBER_MASK) >> Self::ACCOUNT_NUMBER_SHIFT) as u32,
        )
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
    pub fn set_account_number(&mut self, account_number: AccountNumber) {
        self.0 = (self.0 & !(Self::ACCOUNT_NUMBER_MASK << Self::ACCOUNT_NUMBER_SHIFT))
            | ((u64::from(u32::from(account_number)) & Self::ACCOUNT_NUMBER_MASK)
                << Self::ACCOUNT_NUMBER_SHIFT);
    }

    /// Returns the `AccountId` of the `SteamId`.
    #[must_use]
    pub fn account_id(&self) -> AccountId {
        AccountId(((self.0 & Self::ACCOUNT_ID_MASK) >> Self::ACCOUNT_ID_SHIFT) as u32)
    }

    /// Sets the `AccountId` of the `SteamId`.
    pub fn set_account_id(&mut self, account_id: AccountId) {
        self.0 = (self.0 & !(Self::ACCOUNT_ID_MASK << Self::ACCOUNT_ID_SHIFT))
            | ((u64::from(u32::from(account_id)) & Self::ACCOUNT_ID_MASK)
                << Self::ACCOUNT_ID_SHIFT);
    }

    /// Returns the `ParityBit` of the `SteamId`.
    ///
    /// # Panics
    /// This method will not panic, as the parity bit is always valid.
    #[must_use]
    pub fn parity_bit(&self) -> ParityBit {
        // The unwrap is possible because ParityBit covers every case. (0 and 1)
        ParityBit::try_from(((self.0 >> Self::PARITY_BIT_SHIFT) & Self::PARITY_BIT_MASK) as u8)
            .unwrap()
    }

    /// Sets the `ParityBit` of the `SteamId`.
    pub fn set_parity_bit(&mut self, parity_bit: ParityBit) {
        self.0 = (self.0 & !(Self::PARITY_BIT_MASK << Self::PARITY_BIT_SHIFT))
            | (u64::from(u8::from(parity_bit)) << Self::PARITY_BIT_SHIFT);
    }

    /// Returns the steam2id representation of the `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the universe or account number are invalid.
    pub fn try_steam2id(&self) -> Result<String> {
        Ok(format!(
            "STEAM_{}:{}:{}",
            u8::from(self.try_universe()?),
            u8::from(self.parity_bit()),
            u32::from(self.try_account_number()?)
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
        Ok(format!(
            "[{}:{}:{}]",
            char::try_from(self.try_account_type()?)?,
            u8::from(self.try_universe()?),
            u32::from(self.account_id())
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

    /// Returns the community link for the `SteamId`.
    #[must_use]
    pub fn community_link(&self) -> String {
        let mut steamid = *self;
        steamid.set_universe(Universe::Public);
        steamid.set_account_type(AccountType::Individual);
        steamid.set_instance(Instance::Desktop);
        format!("https://steamcommunity.com/profiles/{}", u64::from(steamid))
    }

    /// Parse steam2id into a `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the steam2id is invalid.
    pub fn parse_steam2id<S: AsRef<str>>(
        value: S,
        account_type: AccountType,
        instance: Instance,
    ) -> Result<Self> {
        let value = value.as_ref();

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
            .and_then(|v| Ok(Universe::try_from(v)?))?;
        let parity_bit = parts
            .next()
            .ok_or(Error::ParseError("missing parity_bit"))
            .and_then(|v| {
                v.parse::<u8>()
                    .map_err(|_| Error::ParseError("parity_bit is not an integer"))
            })
            .and_then(|v| Ok(ParityBit::try_from(v)?))?;
        let account_number = parts
            .next()
            .ok_or(Error::ParseError("missing account number"))
            .and_then(|v| {
                v.parse::<u32>()
                    .map_err(|_| Error::ParseError("account number is not an integer"))
            })
            .and_then(AccountNumber::try_from)?;

        SteamId::new(
            u64::from(u8::from(universe)) << Self::UNIVERSE_SHIFT
                | u64::from(u8::from(account_type) & 0xF) << Self::ACCOUNT_TYPE_SHIFT
                | u64::from(u32::from(instance) & 0x7FFF) << Self::INSTANCE_SHIFT
                | u64::from(u32::from(account_number)) << Self::ACCOUNT_NUMBER_SHIFT
                | u64::from(u8::from(parity_bit) & 0x1),
        )
    }

    /// Parse steam3id into a `SteamId`.
    ///
    /// # Errors
    /// This method returns an error if the steam3id is invalid.
    pub fn parse_steam3id<S: AsRef<str>>(value: S, instance: Instance) -> Result<Self> {
        let mut value = value.as_ref();

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
            .ok_or(Error::ParseError("account type should be a character"))
            .and_then(AccountType::try_from)?;
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
            .map(AccountId::from)?;

        SteamId::new(
            u64::from(u8::from(universe)) << Self::UNIVERSE_SHIFT
                | u64::from(u8::from(account_type) & 0xF) << Self::ACCOUNT_TYPE_SHIFT
                | u64::from(u32::from(instance) & 0x7FFF) << Self::INSTANCE_SHIFT
                | u64::from(u32::from(account_id)),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{AccountType, Instance, SteamId, Universe};

    #[test]
    fn steamid_to_others() {
        let steamid = SteamId::new(76_561_197_999_189_721).unwrap();
        assert_eq!(steamid.steam2id(), "STEAM_1:1:19461996");
        assert_eq!(steamid.steam3id(), "[U:1:38923993]");
    }

    #[test]
    fn steamid_from_steam2id() {
        let steamid = SteamId::parse_steam2id(
            "STEAM_1:1:19461996",
            AccountType::Individual,
            Instance::Desktop,
        )
        .unwrap();
        assert_eq!(steamid, SteamId(76_561_197_999_189_721));
    }

    #[test]
    fn steamid_from_steam3id() {
        let steamid = SteamId::parse_steam3id("[U:1:38923993]", Instance::Desktop).unwrap();
        assert_eq!(steamid, SteamId(76_561_197_999_189_721));
    }

    #[test]
    fn steamid_universe_change() {
        let mut steamid = SteamId::new(76_561_197_999_189_721).unwrap();
        assert_eq!(steamid.steam2id(), "STEAM_1:1:19461996");
        assert_eq!(steamid.universe(), Universe::Public);
        steamid.set_universe(Universe::Individual);
        assert_eq!(steamid.universe(), Universe::Individual);
        assert_eq!(steamid.steam2id(), "STEAM_0:1:19461996");
    }

    #[test]
    fn steamid_community_link() {
        let steamid = SteamId::parse_steam2id(
            "STEAM_0:1:19461996",
            AccountType::Individual,
            Instance::Desktop,
        )
        .unwrap();
        assert_eq!(
            steamid.community_link(),
            "https://steamcommunity.com/profiles/76561197999189721"
        );
    }
}
