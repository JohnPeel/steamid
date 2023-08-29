use crate::macros::{bitfields, forward_impl};

/// A raw Steam ID with no type checking.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct RawSteamId(u64);

impl RawSteamId {
    /// Construct a new `RawSteamId`.
    #[must_use]
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    /// Returns the inner `u64`.
    #[must_use]
    pub const fn into_inner(self) -> u64 {
        self.0
    }

    bitfields! {
        u64;

        /// the raw auth server portion of the `SteamId`.
        pub auth_server: u8 = 0, 0;
        /// the raw account number portion of the `SteamId`.
        pub account_number: u32 = 31, 1;
        /// the raw account id portion of the `SteamId`.
        pub account_id: u32 = 31, 0;
        /// the raw instance portion of the `SteamId`.
        pub instance: u32 = 51, 32;
        /// the raw account type portion of the `SteamId`.
        pub account_type: u8 = 55, 52;
        /// the raw universe portion of the `SteamId`.
        pub universe: u8 = 63, 56;

        /// the raw chat flags portion of the `SteamId`.
        pub chat_flags: u32 = 49, 42;
    }
}

forward_impl!(use new; impl From<u64> for RawSteamId);
forward_impl!(use into_inner; impl Into<u64> for RawSteamId);

#[cfg(test)]
mod tests {
    use super::RawSteamId;

    #[test]
    fn raw_sid_has_proper_values() {
        let sid = RawSteamId::from(76_561_197_999_189_721);

        assert_eq!(1, sid.auth_server());
        assert_eq!(19_461_996, sid.account_number());
        assert_eq!(38_923_993, sid.account_id());
        assert_eq!(1, sid.instance());
        assert_eq!(1, sid.account_type());
        assert_eq!(1, sid.universe());

        assert_eq!(0, sid.chat_flags());

        assert_eq!(
            sid.with_instance(crate::Instance::Web.into_u32()),
            RawSteamId::from(76_561_210_884_091_609)
        );
    }
}
