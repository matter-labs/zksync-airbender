#![cfg_attr(not(feature = "prover"), no_std)]
#![cfg_attr(feature = "prover", allow(incomplete_features))]
#![cfg_attr(feature = "prover", feature(generic_const_exprs))]
#![cfg_attr(feature = "prover", feature(allocator_api))]
#![cfg_attr(feature = "prover", feature(maybe_uninit_fill))]
#![cfg_attr(feature = "prover", feature(lazy_type_alias))] // NECESSARY TO AVOID UGLY LIFETIME BOUND ISSUE

#[cfg(feature = "debug_satisfiable")]
pub const DEBUG_QUOTIENT: bool = true;

#[cfg(not(feature = "debug_satisfiable"))]
pub const DEBUG_QUOTIENT: bool = false;

pub mod definitions;
pub mod utils;

pub use common_constants;
pub use cs;
pub use field;
pub use transcript;

#[cfg(feature = "prover")]
pub use fft;
#[cfg(feature = "prover")]
pub use worker;
#[cfg(feature = "prover")]
pub mod cap_holder;
#[cfg(feature = "prover")]
pub mod fsv_fixture;
#[cfg(feature = "prover")]
pub mod gkr;
#[cfg(feature = "prover")]
pub mod merkle_trees;
#[cfg(feature = "prover")]
pub mod nd_source_std;
#[cfg(feature = "prover")]
pub mod query_utils;
#[cfg(feature = "prover")]
pub mod trace_holder;
#[cfg(feature = "prover")]
pub mod tracers;

#[cfg(any(test, feature = "test"))]
pub mod tests;
