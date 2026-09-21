//! Single-file audit point for items this crate consumes from upstream crates
//! (`common_constants`, `field`, `prover`, `setups`).
//!
//! Same convention as `gpu_trace::upstream`: consumers under
//! `execution_prover_model/src/` import upstream items exclusively through
//! `crate::upstream`, so an upstream rename surfaces here rather than at
//! scattered call sites.

// `common_constants` — circuit family indices, delegation CSR numbers, scalars.
pub(crate) use common_constants::TimestampScalar;

// `field` — base field used by the circuit geometry constants.
pub(crate) use field::baby_bear::base::BabyBearField;

// `prover` — the Merkle cap container the memory-commitment protocol carries.
pub(crate) use prover::merkle_trees::MerkleTreeCapVarLength;

// `setups` — compiled-circuit marker types the geometry constants are read from.
pub(crate) use setups::{
    inits_and_teardowns, AddSubLuiAuipcMopCircuit, BigIntDelegationCircuit,
    Blake2sGFunctionDelegationCircuit, Blake2sWithCompressionDelegationCircuit,
    JumpBranchSltCircuit, KeccakSpecial5DelegationCircuit, LoadStoreSubwordOnlyCircuit,
    LoadStoreWordOnlyCircuit, ShiftBinaryCircuit, UnifiedReducedMachineCircuit,
    UnsignedMulDivCircuit,
};
