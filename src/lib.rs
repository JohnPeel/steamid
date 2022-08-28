//! # Steam ID type and accessories
//! 
//! This project provides the `SteamID` type with conversion methods to convert between different Steam ID formats.
//! 
//! Hosted on [GitHub](https://github.com/JohnPeel/steamid-rs).
//! 
//! ## Examples and Usage
//! 
//! ### Initialize from steam64id
//! ```rust
//! # use steamid::SteamID;
//! let steamid = SteamID::new(76561198181797231);
//! ```
//! 
//! ### Parse a steam2id
//! ```rust
//! # use steamid::SteamID;
//! let steamid = SteamID::parse_steam2id("STEAM_0:0:12345")?;
//! ```
//! 
//! ### Parse a steam3id
//! ```rust
//! # use steamid::SteamID;
//! let steamid = SteamID::parse_steam3id("[U:1:12345]")?;
//! ```
//! 
//! ### steam64id to steam2id
//! ```rust
//! # use steamid::SteamID;
//! let steamid = SteamID::new(76561198181797231);
//! let steam2id = steamid.steam2id()?;
//! ```
//! 
//! //! ### steam64id to steam3id
//! ```rust
//! # use steamid::SteamID;
//! let steamid = SteamID::new(76561198181797231);
//! let steam3id = steamid.steam3id()?;
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_crate_level_docs, missing_docs, private_doc_tests, clippy::pedantic)]
#![deny(unsafe_code)]

extern crate alloc;

use core::convert::Infallible;

use alloc::{fmt, format, string::String};

/// Representation of an universe.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

/// Representation of an account type.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
/// Representation of an instance.
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

/// Representation of an account number.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AccountNumber(u32);

/// Representation of an account id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AccountId(u32);

/// Representation of a Steam id.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SteamID(u64);

/// Error type to represent an invalid universe value.
#[derive(Debug, Clone, Copy)]
pub struct InvalidUniverse(u8);

impl fmt::Display for InvalidUniverse {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Invalid universe: {}", self.0)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidUniverse {}

impl TryFrom<u8> for Universe {
    type Error = InvalidUniverse;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        use Universe::{Beta, Developer, Individual, Internal, Public, Rc};
        Ok(match value {
            0 => Individual,
            1 => Public,
            2 => Beta,
            3 => Internal,
            4 => Developer,
            5 => Rc,
            _ => Err(InvalidUniverse(value))?,
        })
    }
}

impl From<Universe> for u8 {
    fn from(value: Universe) -> Self {
        use Universe::{Beta, Developer, Individual, Internal, Public, Rc};
        match value {
            Individual => 0,
            Public => 1,
            Beta => 2,
            Internal => 3,
            Developer => 4,
            Rc => 5,
        }
    }
}

/// Error type to represent an invalid account type.
#[derive(Debug, Clone, Copy)]
pub enum InvalidAccountType {
    /// Invalid value for account type.
    InvalidValue(u8),
    /// Invalid character for account type.
    InvalidChar(char),
}

impl fmt::Display for InvalidAccountType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use InvalidAccountType::{InvalidChar, InvalidValue};
        match self {
            InvalidValue(value) => write!(f, "Invalid account type (u8): {}", value),
            InvalidChar(ch) => write!(f, "Invalid account type (char): {}", ch),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidAccountType {}

impl TryFrom<u8> for AccountType {
    type Error = InvalidAccountType;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        use AccountType::{
            AnonGameServer, AnonUser, Chat, Clan, ContentServer, GameServer, Individual, Invalid,
            Multiseat, P2pSuperSeeder, Pending,
        };
        Ok(match value {
            0 => Invalid,
            1 => Individual,
            2 => Multiseat,
            3 => GameServer,
            4 => AnonGameServer,
            5 => Pending,
            6 => ContentServer,
            7 => Clan,
            8 => Chat,
            9 => P2pSuperSeeder,
            10 => AnonUser,
            _ => Err(InvalidAccountType::InvalidValue(value))?,
        })
    }
}

impl From<AccountType> for u8 {
    fn from(value: AccountType) -> Self {
        use AccountType::{
            AnonGameServer, AnonUser, Chat, Clan, ContentServer, GameServer, Individual, Invalid,
            Multiseat, P2pSuperSeeder, Pending,
        };
        match value {
            Invalid => 0,
            Individual => 1,
            Multiseat => 2,
            GameServer => 3,
            AnonGameServer => 4,
            Pending => 5,
            ContentServer => 6,
            Clan => 7,
            Chat => 8,
            P2pSuperSeeder => 9,
            AnonUser => 10,
        }
    }
}

impl TryFrom<char> for AccountType {
    type Error = InvalidAccountType;

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
            _ => Err(InvalidAccountType::InvalidChar(value))?,
        })
    }
}

impl From<AccountType> for char {
    fn from(value: AccountType) -> Self {
        use AccountType::{
            AnonGameServer, AnonUser, Chat, Clan, ContentServer, GameServer, Individual, Invalid,
            Multiseat, P2pSuperSeeder, Pending,
        };
        match value {
            Invalid => 'I',
            Individual => 'U',
            Multiseat => 'M',
            GameServer => 'G',
            AnonGameServer => 'A',
            Pending => 'P',
            ContentServer => 'C',
            Clan => 'g',
            Chat => 'T',
            P2pSuperSeeder => {
                unimplemented!("P2pSuperSeeder does not have a character representation")
            }
            AnonUser => 'a',
        }
    }
}

/// Error type to represent an invalid instance value.
#[derive(Debug, Clone, Copy)]
pub struct InvalidInstance(u32);

impl fmt::Display for InvalidInstance {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Invalid instance: {}", self.0)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidInstance {}

impl TryFrom<u32> for Instance {
    type Error = InvalidInstance;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        use Instance::{All, Console, Desktop, Web};
        Ok(match value {
            0 => All,
            1 => Desktop,
            2 => Console,
            3 => Web,
            _ => Err(InvalidInstance(value))?,
        })
    }
}

impl From<Instance> for u32 {
    fn from(value: Instance) -> Self {
        use Instance::{All, Console, Desktop, Web};
        match value {
            All => 0,
            Desktop => 1,
            Console => 2,
            Web => 3,
        }
    }
}

/// Error type to represent an invalid account number value.
#[derive(Debug, Clone, Copy)]
pub struct InvalidAccountNumber(u32);

impl fmt::Display for InvalidAccountNumber {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Invalid account number: {}", self.0)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidAccountNumber {}

impl TryFrom<u32> for AccountNumber {
    type Error = InvalidAccountNumber;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value > 0x7FFF_FFFF {
            Err(InvalidAccountNumber(value))?;
        }
        Ok(AccountNumber(value))
    }
}

impl From<AccountNumber> for u32 {
    fn from(value: AccountNumber) -> Self {
        value.0
    }
}

impl From<u32> for AccountId {
    fn from(value: u32) -> Self {
        AccountId(value)
    }
}

impl From<AccountId> for u32 {
    fn from(value: AccountId) -> Self {
        value.0
    }
}

impl From<SteamID> for u64 {
    fn from(value: SteamID) -> Self {
        value.0
    }
}

impl fmt::Debug for SteamID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SteamID")
            .field("value", &self.0)
            .field("universe", &self.universe())
            .field("type", &self.account_type())
            .field("instance", &self.instance())
            .field("account_number", &self.account_number())
            .field("account_id", &self.account_id())
            .finish()
    }
}

impl fmt::Display for SteamID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SteamID({})", &self.0)
    }
}

/// Error type to represent an invalid steam id.
#[derive(Debug)]
pub enum InvalidSteamID {
    /// The universe is invalid.
    InvalidUniverse(InvalidUniverse),
    /// The account type is invalid.
    InvalidAccountType(InvalidAccountType),
    /// The instance is invalid.
    InvalidInstance(InvalidInstance),
    /// The account number is invalid.
    InvalidAccountNumber(InvalidAccountNumber),
    /// The format of the string is invalid.
    InvalidFormat,
    /// There was an issue parsing some number.
    ParseIntError(core::num::ParseIntError),
}

impl fmt::Display for InvalidSteamID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InvalidSteamID::InvalidUniverse(value) => value.fmt(f),
            InvalidSteamID::InvalidAccountType(value) => value.fmt(f),
            InvalidSteamID::InvalidInstance(value) => value.fmt(f),
            InvalidSteamID::InvalidAccountNumber(value) => value.fmt(f),
            InvalidSteamID::InvalidFormat => write!(f, "Invalid SteamID format"),
            InvalidSteamID::ParseIntError(value) => value.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidSteamID {}

impl From<InvalidUniverse> for InvalidSteamID {
    fn from(value: InvalidUniverse) -> Self {
        InvalidSteamID::InvalidUniverse(value)
    }
}

impl From<InvalidAccountType> for InvalidSteamID {
    fn from(value: InvalidAccountType) -> Self {
        InvalidSteamID::InvalidAccountType(value)
    }
}

impl From<InvalidInstance> for InvalidSteamID {
    fn from(value: InvalidInstance) -> Self {
        InvalidSteamID::InvalidInstance(value)
    }
}

impl From<InvalidAccountNumber> for InvalidSteamID {
    fn from(value: InvalidAccountNumber) -> Self {
        InvalidSteamID::InvalidAccountNumber(value)
    }
}

impl From<core::num::ParseIntError> for InvalidSteamID {
    fn from(value: core::num::ParseIntError) -> Self {
        InvalidSteamID::ParseIntError(value)
    }
}

impl From<Infallible> for InvalidSteamID {
    fn from(_: Infallible) -> Self {
        unreachable!()
    }
}

impl AccountId {
    /// Returns the `AccountNumber` of the `AccountId`.
    /// 
    /// # Errors
    /// Returns `InvalidAccountNumber` if the account number is invalid.
    pub fn account_number(&self) -> Result<AccountNumber, InvalidAccountNumber> {
        ((self.0 >> 1) as u32).try_into()
    }
}

impl SteamID {
    /// Constructs a new `SteamID` from the steam64id.
    #[must_use]
    pub fn new(steam64id: u64) -> Self {
        // TODO: We should validate the steam64id here, and remove the errors for the other methods.
        SteamID(steam64id)
    }

    /// Returns the `Universe` of the `SteamID`.
    /// 
    /// # Errors
    /// Returns `InvalidUniverse` if the universe is invalid.
    pub fn universe(&self) -> Result<Universe, InvalidUniverse> {
        (((self.0 >> 56) & 0xFF) as u8).try_into()
    }

    /// Returns the account type of the `SteamID`.
    /// 
    /// # Errors
    /// Returns `InvalidAccountType` if the account type is invalid.
    pub fn account_type(&self) -> Result<AccountType, InvalidAccountType> {
        (((self.0 >> 52) & 0xF) as u8).try_into()
    }

    /// Returns the instance of the `SteamID`.
    /// 
    /// # Errors
    /// Returns `InvalidInstance` if the instance is invalid.
    pub fn instance(&self) -> Result<Instance, InvalidInstance> {
        (((self.0 >> 32) & 0xFFFFF) as u32).try_into()
    }

    /// Returns the `AccountNumber` of the `SteamID`.
    /// 
    /// # Errors
    /// Returns `InvalidAccountNumber` if the account number is invalid.
    pub fn account_number(&self) -> Result<AccountNumber, InvalidAccountNumber> {
        (((self.0 & 0xFFFF_FFFF) >> 1) as u32).try_into()
    }

    /// Returns the `AccountId` of the `SteamID`.
    /// 
    /// # Errors
    /// This method is currently infallible, but may return an error in the future.
    pub fn account_id(&self) -> Result<AccountId, Infallible> {
        ((self.0 & 0xFFFF_FFFF) as u32).try_into()
    }

    /// Returns the steam2id representation of the `SteamID`.
    /// 
    /// # Errors
    /// Returns `InvalidSteamID` if the `SteamID` is invalid.
    pub fn steam2id(&self) -> Result<String, InvalidSteamID> {
        Ok(format!(
            "STEAM_{}:{}:{}",
            u8::from(self.universe()?),
            self.0 & 0x1,
            u32::from(self.account_number()?)
        ))
    }

    /// Returns the steam3id representation of the `SteamID`.
    /// 
    /// # Errors
    /// Returns `InvalidSteamID` if the `SteamID` is invalid.
    pub fn steam3id(&self) -> Result<String, InvalidSteamID> {
        Ok(format!(
            "[{}:{}:{}]",
            char::from(self.account_type()?),
            u8::from(self.universe()?),
            u32::from(self.account_id()?)
        ))
    }

    /// Returns the `SteamID` as a 64-bit integer.
    #[must_use]
    pub fn steam64id(&self) -> u64 {
        self.0
    }

    /// Parse steam2id into a `SteamID`.
    /// 
    /// # Errors
    /// Returns `InvalidSteamID` if the steam2id is invalid.
    pub fn parse_steam2id<S: AsRef<str>>(
        value: S,
        account_type: AccountType,
        instance: Instance,
    ) -> Result<Self, InvalidSteamID> {
        use InvalidSteamID::InvalidFormat;

        let value = value.as_ref();

        if !value.starts_with("STEAM_") {
            return Err(InvalidFormat);
        }

        let mut parts = value[6..].split(':');

        let universe = Universe::try_from(parts.next().ok_or(InvalidFormat)?.parse::<u8>()?)?;
        let id = u64::from(parts.next().ok_or(InvalidFormat)?.parse::<u8>()?);
        let account_number =
            AccountNumber::try_from(parts.next().ok_or(InvalidFormat)?.parse::<u32>()?)?;

        Ok(SteamID(
            (u64::from(u8::from(universe)) << 56)
                | (u64::from(u8::from(account_type) & 0xF) << 52)
                | (u64::from(u32::from(instance) & 0x7FFF) << 32)
                | (u64::from(u32::from(account_number)) << 0x1)
                | (id & 0x1),
        ))
    }

    /// Parse steam3id into a `SteamID`.
    /// 
    /// # Errors
    /// Returns `InvalidSteamID` if the steam3id is invalid.
    pub fn parse_steam3id<S: AsRef<str>>(
        value: S,
        instance: Instance,
    ) -> Result<Self, InvalidSteamID> {
        use InvalidSteamID::InvalidFormat;

        let value = value.as_ref();

        if !value.starts_with('[') || !value.ends_with(']') {
            return Err(InvalidFormat);
        }

        let mut parts = value[1..value.len() - 1].split(':');

        let account_type = parts.next().ok_or(InvalidFormat)?;
        if account_type.len() != 1 {
            return Err(InvalidFormat);
        }
        let account_type =
            AccountType::try_from(account_type.chars().next().ok_or(InvalidFormat)?)?;
        let universe = Universe::try_from(parts.next().ok_or(InvalidFormat)?.parse::<u8>()?)?;
        let account_id = AccountId::try_from(parts.next().ok_or(InvalidFormat)?.parse::<u32>()?)?;

        let id = account_id.0 & 0x1;
        let account_number = account_id.account_number()?;

        Ok(SteamID(
            (u64::from(u8::from(universe)) << 56)
                | (u64::from(u8::from(account_type) & 0xF) << 52)
                | (u64::from(u32::from(instance) & 0x7FFF) << 32)
                | (u64::from(u32::from(account_number)) << 0x1)
                | u64::from(id),
        ))
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;

    use super::{AccountType, Instance, SteamID};

    #[test]
    fn steamid_to_others() {
        let steamid = SteamID(76_561_197_999_189_721);
        assert_eq!(steamid.steam2id().unwrap(), "STEAM_1:1:19461996");
        assert_eq!(steamid.steam3id().unwrap(), "[U:1:38923993]");
    }

    #[test]
    fn steamid_from_steam2id() {
        let steamid = SteamID::parse_steam2id(
            "STEAM_1:1:19461996",
            AccountType::Individual,
            Instance::Desktop,
        )
        .unwrap();
        assert_eq!(steamid, SteamID(76_561_197_999_189_721));
    }

    #[test]
    fn steamid_from_steam3id() {
        let steamid = SteamID::parse_steam3id("[U:1:38923993]", Instance::Desktop).unwrap();
        assert_eq!(steamid, SteamID(76_561_197_999_189_721));
    }

    #[test]
    fn steamid_debug() {
        let steamid = SteamID(76_561_197_999_189_721);
        assert_eq!(
            format!("{:?}", steamid),
            "SteamID { value: 76561197999189721, universe: Ok(Public), type: Ok(Individual), instance: Ok(Desktop), account_number: Ok(AccountNumber(19461996)), account_id: Ok(AccountId(38923993)) }"
        );
    }
}
