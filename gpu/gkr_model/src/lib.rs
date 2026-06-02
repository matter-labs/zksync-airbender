//! GPU-free CPU model of the GKR layout (address audit, storage layout,
//! circuit transform), extracted from `circuit_prover` so it builds and tests
//! without CUDA. Depends only on `cs` + `field`.

mod upstream;

pub mod address_audit;
pub mod storage_layout;
pub mod transform;
