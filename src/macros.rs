macro_rules! forward_impl {
    (use $method:ident; impl From<$ty:ty> for $self:ty) => {
        impl From<$ty> for $self {
            #[must_use]
            fn from(value: $ty) -> Self {
                Self::$method(value)
            }
        }
    };
    (use $method:ident; impl Into<$ty:ty> for $self:ty) => {
        impl From<$self> for $ty {
            #[must_use]
            fn from(value: $self) -> Self {
                <$self>::$method(value)
            }
        }
    };
    (use $method:ident; impl TryFrom<$ty:ty, Error = $error:ty> for $ident:ty) => {
        impl TryFrom<$ty> for $ident {
            type Error = $error;

            fn try_from(value: $ty) -> Result<Self, Self::Error> {
                Self::$method(value)
            }
        }
    };

    (use $method:ident; impl TryInto<$ident:ty, Error = $error:ty> for $ty:ty) => {
        impl TryFrom<$ty> for $ident {
            type Error = $error;

            fn try_from(value: $ty) -> Result<Self, Self::Error> {
                <$ty>::$method(value)
            }
        }
    };
}
pub(crate) use forward_impl;

macro_rules! bitfields {
    ($host_ty:ty; $(#[doc = $doc:literal] $(#[$meta:meta])* $vis:vis $ident:ident: $ty:ty = $msb:expr, $lsb:expr);+;) => {$(
        paste::paste! {
            const [<$ident:upper _MASK>]: $host_ty = (1 << ( [<$msb _ $host_ty>] - [<$lsb _ $host_ty>] + 1 )) - 1;
            const [<$ident:upper _SHIFT>]: $host_ty = $lsb;

            #[doc = concat!("Sets ", $doc)]
            $(#[$meta])*
            #[must_use]
            $vis const fn [<with_ $ident>](self, value: $ty) -> Self {
                Self((self.0 & !(Self::[<$ident:upper _MASK>] << Self::[<$ident:upper _SHIFT>])) | (((value as $host_ty) & Self::[<$ident:upper _MASK>]) << Self::[<$ident:upper _SHIFT>]))
            }

            #[doc = concat!("Returns ", $doc)]
            $(#[$meta])*
            #[must_use]
            $vis const fn $ident(self) -> $ty {
                ((self.0 >> Self::[<$ident:upper _SHIFT>]) & Self::[<$ident:upper _MASK>]) as $ty
            }
        }
    )+};
}
pub(crate) use bitfields;
