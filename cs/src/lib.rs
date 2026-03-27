#![cfg_attr(not(feature = "compiler"), no_std)]
#![allow(type_alias_bounds)]
#![feature(allocator_api)]

pub mod definitions;

#[cfg(feature = "compiler")]
pub mod constraint;
#[cfg(feature = "compiler")]
pub mod cs;
// #[cfg(feature = "compiler")]
// pub mod delegation;
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
