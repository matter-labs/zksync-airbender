use crate::definitions::*;

pub mod circuit;
pub mod circuit_impl;
pub mod circuit_output;
pub mod circuit_trait;
pub mod lookup_input;
pub mod lookup_utils;
pub mod utils;

pub const DEFAULT_SOURCE_DEST_CAPACITY: usize = 4;
#[cfg(feature = "debug_logs")]
pub const ENABLE_LOGGING: bool = true;
#[cfg(not(feature = "debug_logs"))]
pub const ENABLE_LOGGING: bool = false;
