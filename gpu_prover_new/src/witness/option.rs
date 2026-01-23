pub mod u8 {
    #[repr(C, u8)]
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

pub mod u32 {
    #[repr(C, u32)]
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
