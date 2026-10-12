mod commit;
mod in_domain;
mod kernels;
mod openings;
pub mod outputs;
pub mod schedule;
mod shape;
mod state;

pub use outputs::{L1WhirProof, L1WhirScheduled};
pub use schedule::{schedule_l1_whir_fold, L1WhirInputs};
pub use shape::{L1WhirShape, OracleShape, RoundShape, L1_WHIR_TILE_BYTES};

const _: () = {
    assert!(crate::upstream::EVM_PRODUCTION_TRACE_LEN_LOG2 == 22);
    assert!(crate::upstream::EVM_PRODUCTION_PACK_LOG2 == 4);
};

#[cfg(test)]
mod tests;
