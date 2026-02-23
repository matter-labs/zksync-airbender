#![cfg_attr(not(feature = "prover"), no_std)]
#![cfg_attr(feature = "prover", allow(incomplete_features))]
#![cfg_attr(feature = "prover", feature(generic_const_exprs))]
#![cfg_attr(feature = "prover", feature(allocator_api))]
#![cfg_attr(feature = "prover", feature(iter_array_chunks))]
#![cfg_attr(feature = "prover", feature(raw_slice_split))]
#![cfg_attr(feature = "prover", feature(slice_from_ptr_range))]
#![cfg_attr(feature = "prover", feature(vec_push_within_capacity))]
#![cfg_attr(feature = "prover", feature(maybe_uninit_fill))]
#![cfg_attr(feature = "prover", feature(lazy_type_alias))] // NECESSARY TO AVOID UGLY LIFETIME BOUND ISSUE

#[cfg(feature = "debug_satisfiable")]
pub const DEBUG_QUOTIENT: bool = true;

#[cfg(not(feature = "debug_satisfiable"))]
pub const DEBUG_QUOTIENT: bool = false;

#[cfg(feature = "prover")]
pub const DEFAULT_TRACE_PADDING_MULTIPLE: usize = 32;

pub mod definitions;
pub use common_constants;
pub use cs;
pub use field;
pub use transcript;

#[cfg(feature = "prover")]
pub use trace_holder;

#[cfg(feature = "prover")]
pub use fft;
#[cfg(feature = "prover")]
pub use worker;

#[cfg(feature = "prover")]
pub mod cap_holder;
#[cfg(feature = "prover")]
pub mod gkr;
#[cfg(feature = "prover")]
pub mod mem_utils;
#[cfg(feature = "prover")]
pub mod merkle_trees;
#[cfg(feature = "prover")]
pub mod nd_source_std;
#[cfg(feature = "prover")]
pub mod prover_stages;
#[cfg(feature = "prover")]
pub mod quotient_evaluator;
#[cfg(feature = "prover")]
pub mod tracer;
#[cfg(feature = "prover")]
pub mod tracers;
pub mod utils;
#[cfg(feature = "prover")]
pub mod witness_evaluator;

#[cfg(feature = "prover")]
pub use self::quotient_evaluator::*;
#[cfg(feature = "prover")]
pub use self::tracer::*;
#[cfg(feature = "prover")]
pub use self::witness_evaluator::*;
#[cfg(feature = "prover")]
pub use risc_v_simulator;

#[cfg(any(test, feature = "test"))]
pub mod tests;
