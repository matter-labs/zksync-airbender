macro_rules! option_repr {
    ($repr:ident) => {
        pub mod $repr {
            #[repr(C, $repr)]
            #[derive(Copy, Clone, Default, Debug)]
            pub enum Option<T> {
                #[default]
                None,
                Some(T),
            }

            impl<T, U> From<core::option::Option<T>> for Option<U>
            where
                T: Into<U>,
            {
                fn from(option: core::option::Option<T>) -> Self {
                    match option {
                        Some(value) => Self::Some(value.into()),
                        None => Self::None,
                    }
                }
            }
        }
    };
}

option_repr!(u8);
option_repr!(u32);
