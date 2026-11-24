use crate::upstream::Proth120;

pub type Proth120Field = Proth120;

pub type PR = Proth120Field;

const _: () = {
    assert!(core::mem::size_of::<PR>() == 16);
    assert!(core::mem::align_of::<PR>() == 16);
};
