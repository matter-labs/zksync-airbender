//! Forward VM compiler and 16-bit-lane encoding for `gkr_eval_ir`.
pub(crate) mod artifact;
pub(crate) mod binding;
pub(crate) mod compile;
pub(crate) mod context;
pub(crate) mod encode;
pub(crate) mod error;
pub(crate) mod isa;
#[cfg(feature = "search")]
pub(crate) mod search;
pub(crate) mod source;
pub(crate) mod stats;
pub(crate) mod validate;

pub(crate) const BF_LANES_PER_E4_BUCKET: usize = 4;
pub(crate) const BABYBEAR_NEG_ONE: u32 = 0x78000000;
