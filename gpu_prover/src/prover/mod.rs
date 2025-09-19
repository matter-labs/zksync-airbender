pub(crate) mod arg_utils;
mod callbacks;
pub mod context;
mod device_tracing;
pub mod memory;
mod pow;
pub(crate) mod precomputations;
pub mod proof;
mod queries;
pub mod setup;
pub(crate) mod stage_1;
mod stage_2;
mod stage_2_kernels;
mod stage_3;
mod stage_3_kernels;
mod stage_4;
mod stage_4_kernels;
mod stage_5;
pub mod trace_holder;
pub mod tracing_data;
pub mod transfer;

use field::{Mersenne31Complex, Mersenne31Field, Mersenne31Quartic};

type BF = Mersenne31Field;
type E2 = Mersenne31Complex;
type E4 = Mersenne31Quartic;
