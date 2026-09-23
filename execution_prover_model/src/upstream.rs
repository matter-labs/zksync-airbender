//! Upstream imports for the shared host model. Consumers use `crate::upstream`
//! so upstream API changes surface in one place.

// `common_constants` — circuit family indices, delegation CSR numbers, scalars.
pub(crate) use common_constants::TimestampScalar;

// `field` — base field used by the circuit geometry constants.
pub(crate) use field::baby_bear::base::BabyBearField;

// `setups` — compiled-circuit marker types the geometry constants are read from.
pub(crate) use setups::{
    inits_and_teardowns, AddSubLuiAuipcMopCircuit, BigIntDelegationCircuit,
    Blake2sGFunctionDelegationCircuit, Blake2sWithCompressionDelegationCircuit,
    JumpBranchSltCircuit, KeccakSpecial5DelegationCircuit, LoadStoreSubwordOnlyCircuit,
    LoadStoreWordOnlyCircuit, ShiftBinaryCircuit, UnifiedReducedMachineCircuit,
    UnsignedMulDivCircuit,
};
