//! Instruction-level algebraic circuits
//! ===================================
//!
//! This `ops` module contains one circuit implementation per RISC-V instruction
//! family.  Each sub-module exposes a type that implements the
//! MachineOp trait, making it connected to the high-level machine compiler.
//! Tables for expensive logic: byte-wise ops, multiplication, division
//! and other non-linear behaviour rely on pre-computed lookup tables (look at
//! TableType::*).
//! OptimizationContext – gadgets which deduplicates identical lookups and aggregates
//!   multibyte relations to lower constraint cost.
use super::*;

pub mod add_sub;
pub mod binops;
pub mod conditional;
pub mod constants;
pub mod csr;
pub mod jump;
pub mod lui_auipc;
// pub mod memory;
pub mod load;
pub mod mop;
pub mod mul_div;
pub mod shift;
pub mod store;

pub mod common_impls;

pub const RS1_LOAD_LOCAL_TIMESTAMP: usize = 0;
pub const RS2_LOAD_LOCAL_TIMESTAMP: usize = 1;
pub const RD_STORE_LOCAL_TIMESTAMP: usize = 2;

pub use self::add_sub::*;
pub use self::binops::*;
pub use self::conditional::*;
pub use self::constants::*;
pub use self::csr::*;
pub use self::jump::*;
pub use self::lui_auipc::*;
// pub use self::memory::*;
pub use self::load::*;
pub use self::mop::*;
pub use self::mul_div::*;
pub use self::shift::*;
pub use self::store::*;

pub use self::common_impls::*;

use devices::diffs::NextPcValue;
