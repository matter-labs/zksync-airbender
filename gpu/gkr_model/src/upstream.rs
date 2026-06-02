//! Re-export manifest mirroring `circuit_prover`'s convention, so the moved
//! files keep `use crate::upstream::…` unchanged. Paths are copied verbatim
//! from `gpu/circuit_prover/src/upstream.rs`.

pub(crate) use cs::definitions::gkr::{
    NoFieldLinearRelation, NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
    RamWordRepresentation,
};
pub(crate) use cs::definitions::GKRAddress;
pub(crate) use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRCircuitArtifact, NoFieldGKRCacheRelation, NoFieldGKRRelation,
    NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation,
    NoFieldSpecialMemoryContributionRelation, OutputType,
};
pub(crate) use field::PrimeField;
