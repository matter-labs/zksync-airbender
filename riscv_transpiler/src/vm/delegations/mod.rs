use super::*;
use crate::vm::instructions::*;

// NOTE: there is default += TIMESTAMP_STEP on the outer cycle, so we should always adjust timestamp a little less in implementations

pub mod bigint;
pub mod blake2_round_function;
pub mod keccak_special5;
