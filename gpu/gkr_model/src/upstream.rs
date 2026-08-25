//! Re-export manifest mirroring `gpu_circuit_prover`'s convention, so the moved
//! files keep `use crate::upstream::…` unchanged. Paths are copied verbatim
//! from `gpu/circuit_prover/src/upstream.rs`.

pub(crate) use cs::definitions::gkr::{
    LinearRelation, RamWordRepresentation, SingleColumnLookupRelation, VectorLookupRelation,
};
pub(crate) use cs::definitions::GKRAddress;
pub(crate) use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMaxQuadraticGKRRelation,
    CompiledMemoryTimestamp, GKRCacheRelation, GKRCircuitArtifact, GKRRelation,
    InitsOrTeardownsTimestampAndValue, MaxQuadraticConstraintsGKRRelation, OutputType,
    SpecialMemoryContributionRelation,
};
pub(crate) use field::PrimeField;
