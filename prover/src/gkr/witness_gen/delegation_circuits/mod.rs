use super::*;

use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
use common_constants::{TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use cs::definitions::gkr::NoFieldLinearRelation;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::oracle::Oracle;
use cs::utils::split_timestamp;
use field::PrimeField;
use worker::WorkerGeometry;

mod memory;
mod witness;

pub use self::memory::evaluate_gkr_memory_witness_for_delegation_circuit;
pub use self::witness::evaluate_gkr_witness_for_delegation_circuit;
