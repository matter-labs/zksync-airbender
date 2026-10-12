mod commit;
mod kernels;
mod openings;
pub mod outputs;
mod shape;
mod state;

pub use shape::{L1WhirShape, OracleShape, RoundShape, L1_WHIR_TILE_BYTES};

const _: () = {
    assert!(crate::upstream::EVM_PRODUCTION_TRACE_LEN_LOG2 == 22);
    assert!(crate::upstream::EVM_PRODUCTION_PACK_LOG2 == 4);
};

#[cfg(test)]
mod tests;
