use derive_more::{From, Into};
use paste::paste;

macro_rules! bitfields {
    ($host_ty:ty; $($(#[$meta:meta])* $vis:vis $ident:ident: $ty:ty = $msb:expr, $lsb:expr);+;) => {$(
        paste! {
            const [<$ident:upper _MASK>]: $host_ty = (1 << ( [<$msb _ $host_ty>] - [<$lsb _ $host_ty>] + 1 )) - 1;
            const [<$ident:upper _SHIFT>]: $host_ty = $lsb;

            $(#[$meta])*
            #[inline]
            #[must_use]
            $vis const fn [<with_ $ident>](self, value: $ty) -> Self {
                Self((self.0 & !(Self::[<$ident:upper _MASK>] << Self::[<$ident:upper _SHIFT>])) | (((value as $host_ty) & Self::[<$ident:upper _MASK>]) << Self::[<$ident:upper _SHIFT>]))
            }

            $(#[$meta])*
            #[inline]
            #[must_use]
            $vis const fn $ident(self) -> $ty {
                ((self.0 >> Self::[<$ident:upper _SHIFT>]) & Self::[<$ident:upper _MASK>]) as $ty
            }
        }
    )+};
}

/// Raw representation of a Steam id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(From, Into)]
#[repr(transparent)]
pub struct SteamId(u64);

impl SteamId {
    /// Construct a new `SteamId` from a [`u64`].
    #[inline]
    #[must_use]
    pub const fn new(steam_id: u64) -> Self {
        Self(steam_id)
    }

    /// Returns the raw `u64` representation of the `SteamId`.
    #[inline]
    #[must_use]
    pub const fn raw(self) -> u64 {
        self.0
    }

    bitfields! {
        u64;

        /// The raw auth server portion of the `SteamId`.
        pub auth_server: u8 = 0, 0;
        /// The raw account number portion of the `SteamId`.
        pub account_number: u32 = 31, 1;
        /// The raw account id portion of the `SteamId`.
        pub account_id: u32 = 31, 0;
        /// The raw instance portion of the `SteamId`.
        pub instance: u32 = 51, 32;
        /// The raw account type portion of the `SteamId`.
        pub account_type: u8 = 55, 52;
        /// The raw universe portion of the `SteamId`.
        pub universe: u8 = 63, 56;

        /// The raw chat flags portion of the `SteamId`.
        pub chat_flags: u32 = 49, 42;
    }
}

#[test]
fn raw_sid_has_proper_values() {
    let sid = SteamId::from(76_561_197_999_189_721);

    assert_eq!(1, sid.auth_server());
    assert_eq!(19_461_996, sid.account_number());
    assert_eq!(38_923_993, sid.account_id());
    assert_eq!(1, sid.instance());
    assert_eq!(1, sid.account_type());
    assert_eq!(1, sid.universe());

    assert_eq!(0, sid.chat_flags());
}
