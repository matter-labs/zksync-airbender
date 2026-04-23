#![cfg_attr(not(feature = "compiler"), no_std)]
#![cfg_attr(feature = "compiler", feature(allocator_api))]
#![cfg_attr(feature = "compiler", allow(type_alias_bounds))]

pub mod definitions;

#[cfg(feature = "compiler")]
pub mod constraint;
#[cfg(feature = "compiler")]
pub mod cs;
#[cfg(feature = "compiler")]
pub mod gkr_circuits;
#[cfg(feature = "compiler")]
pub mod gkr_compiler;
#[cfg(feature = "compiler")]
pub mod oracle;
#[cfg(feature = "compiler")]
pub mod tables;
#[cfg(feature = "compiler")]
pub mod types;
#[cfg(feature = "compiler")]
pub mod utils;
#[cfg(feature = "compiler")]
pub mod witness_placer;
