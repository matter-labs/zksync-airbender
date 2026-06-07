//! Task 13 — guarded prover-side cross-validation of codegen IR metadata.
//!
//! Two invariant families are checked, guarded so no panic can occur:
//!
//! (a) `num_challenges` for the ~5 `NoFieldGKRRelation` variants that
//!     `cs::NoFieldGKRRelation::num_challenges()` hits its `panic!` catch-all on.
//!     For each we build the kernel struct directly (NOT via `from_enforced_relations`
//!     which needs runtime state and also panics on some variants) and compare
//!     `cs::gkr_compiler::codegen_ir::relation_metadata(rel).num_challenges`
//!     against `BatchedGKRKernel::num_challenges()`.
//!
//! (b) Per-operand domain for variants whose kernel implements `get_inputs()`.
//!     We call `kernel.get_inputs()` and assert that addresses the cs IR lowering
//!     resolves as `Domain::Base` are in `inputs_in_base`, and those resolved as
//!     `Domain::Ext` are in `inputs_in_extension`.
//!
//! # GET_INPUTS_IMPLEMENTED (non-panicking get_inputs):
//!   - LookupPairGKRRelation                               (AggregateLookupRationalPair)
//!   - LookupBasePairGKRRelation                           (LookupPairFromMaterializedBaseInputs)
//!   - LookupBaseMinusMultiplicityByBaseGKRRelation        (LookupFromMaterializedBaseInputWithSetup)
//!   - LookupExtensionMinusMultiplicityByExtensionGKRRelation (LookupFromMaterializedVectorInputWithSetup)
//!   - LookupRationalPairWithUnbalancedBaseGKRRelation     (LookupUnbalancedPairWithMaterializedBaseInputs)
//!   - LookupRationalPairWithUnbalancedExtensionGKRRelation (LookupUnbalancedPairWithMaterializedVectorInputs)
//!   - LookupBaseExtMinusBaseExtGKRRelation                (LookupWithCachedDensAndSetup)
//!   - MaskIntoIdentityProductGKRRelation                  (MaskIntoIdentityProduct)
//!
//! # NUM_CHALLENGES_UNCOVERED_BY_CS (panic in cs::num_challenges()):
//!   - MaterializeGrandProductTermExpression → MaterializeMemoryTermGKRRelation   (1)
//!   - LookupFromVectorInputWithSetup → LookupExtensionMinusMultiplicityByExtensionWithoutCachesGKRRelation (2)
//!   - LookupUnbalancedPairWithVectorInputs → LookupRationalPairWithUnbalancedExtensionWithoutCachesGKRRelation (2)
//!   - LookupUnbalancedPairWithMaterializedVectorInputs → LookupRationalPairWithUnbalancedExtensionGKRRelation (2) [also in GET_INPUTS_IMPLEMENTED]
//!   - InitsOrTeardownsInitialPair → InitsAndTeardownsInitialProductWithoutCachesGKRRelation (1)
//!
//! # UNVALIDATED_BY_CONSTRUCTION (no panic, no false-green claim):
//! These variants have no kernel in GET_INPUTS_IMPLEMENTED *and* their cs num_challenges()
//! is already tested by the Task 2 cs-side test (they do NOT panic in cs::num_challenges()):
//!   - LinearBaseFieldRelation      (cs num_challenges=1, no get_inputs)
//!   - MaxQuadratic                 (cs num_challenges=1, no get_inputs)
//!   - EnforceSingleMaxQuadraticConstraint (cs num_challenges=1, no get_inputs)
//!   - EnforceConstraintsMaxQuadratic      (cs num_challenges=1, no get_inputs — "no longer supported")
//!   - CopyInBaseField              (cs num_challenges=1, BaseFieldCopyGKRRelation get_inputs returns empty)
//!   - CopyInExtensionField         (cs num_challenges=1, ExtensionCopyGKRRelation get_inputs returns empty)
//!   - InitialGrandProductFromCaches (cs num_challenges=1, SameSizeProductGKRRelation get_inputs: unreachable!)
//!   - InitialGrandProductWithoutCaches (cs num_challenges=1, SameSizeProductGKRRelationWithoutCaches get_inputs: unreachable!)
//!   - UnbalancedGrandProductWithCache  (cs num_challenges=1, no direct single-kernel)
//!   - TrivialProduct               (cs num_challenges=1, same kernel as InitialGrandProductFromCaches)
//!   - MaterializeSingleLookupInput (cs num_challenges=1, get_inputs: unimplemented!)
//!   - MaterializedVectorLookupInput (cs num_challenges=1, get_inputs: unreachable!)
//!   - LookupWithCachedDensAndSetup (cs num_challenges=2, LookupBaseExtMinusBaseExtGKRRelation — covered by (b))
//!   - LookupWithDensAndSetupExpressions (cs num_challenges=2, LookupBaseExtMinusBaseExtWithoutCachesGKRRelation get_inputs: unimplemented!)
//!   - LookupWithDensAndCachedSetup (cs num_challenges=2, LookupBaseExtNoCacheMinusBaseExtWithCacheGKRRelation get_inputs: unimplemented!)
//!   - LookupPairFromBaseInputs     (cs num_challenges=2, LookupBasePairWithoutCachesGKRRelation get_inputs: unimplemented!)
//!   - LookupPairFromVectorInputs   (cs num_challenges=2, LookupExtensionPairWithoutCachesGKRRelation get_inputs: unimplemented!)
//!   - LookupPairFromMaterializedVectorInputs (cs num_challenges=2, LookupExtensionPairGKRRelation get_inputs: implemented)
//!   - LookupPairFromCachedVectorInputs       (cs num_challenges=2, same kernel as LookupPairFromMaterializedVectorInputs)
//!   - LookupUnbalancedPairWithMaterializedBaseInputs (cs num_challenges=2) — covered under (b) via LookupRationalPairWithUnbalancedBaseGKRRelation

use cs::definitions::gkr::{
    NoFieldLinearRelation, NoFieldVectorLookupRelation, RamWordRepresentation,
};
use cs::definitions::GKRAddress;
use cs::gkr_compiler::{
    codegen_ir::relation_metadata, CompiledAddressSpaceRelationStrict, CompiledAddressStrict,
    CompiledMemoryTimestamp, InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation,
    NoFieldSpecialMemoryContributionRelation,
};
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic, PrimeField};

use crate::gkr::sumcheck::evaluation_kernels::{
    BatchedGKRKernel, InitsAndTeardownsInitialProductWithoutCachesGKRRelation,
    LookupBaseExtMinusBaseExtGKRRelation, LookupBaseMinusMultiplicityByBaseGKRRelation,
    LookupBasePairGKRRelation, LookupExtensionMinusMultiplicityByExtensionGKRRelation,
    LookupExtensionMinusMultiplicityByExtensionWithoutCachesGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation,
    LookupRationalPairWithUnbalancedExtensionWithoutCachesGKRRelation,
    MaskIntoIdentityProductGKRRelation, MaterializeMemoryTermGKRRelation,
};

type F = Mersenne31Field;
type E = Mersenne31Quartic;

/// Convenience: make a `GKRAddress::InnerLayer` address with a fixed layer index.
fn addr(n: usize) -> GKRAddress {
    GKRAddress::InnerLayer { layer: 1, offset: n }
}

/// Helper: assert that every address the cs lowering treats as Base
/// is in `inputs_in_base`, and every address treated as Ext is in
/// `inputs_in_extension`. Call `get_inputs()` inside the guard because
/// it only applies to kernels in GET_INPUTS_IMPLEMENTED.
fn assert_domains_match(
    base_addrs: &[GKRAddress],
    ext_addrs: &[GKRAddress],
    inputs_in_base: &[GKRAddress],
    inputs_in_extension: &[GKRAddress],
    variant_name: &str,
) {
    for a in base_addrs {
        assert!(
            inputs_in_base.contains(a),
            "{}: cs says {:?} is Base but kernel does not have it in inputs_in_base (got {:?})",
            variant_name, a, inputs_in_base,
        );
    }
    for a in ext_addrs {
        assert!(
            inputs_in_extension.contains(a),
            "{}: cs says {:?} is Ext but kernel does not have it in inputs_in_extension (got {:?})",
            variant_name, a, inputs_in_extension,
        );
    }
}

// ---------------------------------------------------------------------------
// (a) num_challenges cross-validation for the 5 cs-panicking variants
// ---------------------------------------------------------------------------

#[test]
fn num_challenges_materialized_grand_product_term_expression() {
    // MaterializeGrandProductTermExpression → MaterializeMemoryTermGKRRelation (num_challenges = 1)
    // cs::num_challenges() panics on this variant.
    let mem_contrib = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::Constant(1),
        address: CompiledAddressStrict::Constant(42),
        timestamp: CompiledMemoryTimestamp::Zero,
        value: RamWordRepresentation::Zero,
        timestamp_offset: 0,
    };
    let rel = NoFieldGKRRelation::MaterializeGrandProductTermExpression {
        input: mem_contrib.clone(),
        output: addr(0),
    };
    let kernel = MaterializeMemoryTermGKRRelation {
        relation: mem_contrib,
        output: addr(0),
    };

    let cs_meta = relation_metadata(&rel);
    let prover_nc = BatchedGKRKernel::<F, E>::num_challenges(&kernel);
    assert_eq!(
        cs_meta.num_challenges as usize, prover_nc,
        "MaterializeGrandProductTermExpression num_challenges mismatch"
    );
}

#[test]
fn num_challenges_inits_or_teardowns_initial_pair() {
    // InitsOrTeardownsInitialPair → InitsAndTeardownsInitialProductWithoutCachesGKRRelation (num_challenges = 1)
    // cs::num_challenges() panics on this variant.
    let rel = NoFieldGKRRelation::InitsOrTeardownsInitialPair {
        timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
        setup: [addr(10), addr(11)],
        output: addr(20),
        set_idxes: [0, 1],
    };
    // Construct with dummy address_high_bits (not used in num_challenges).
    let kernel = InitsAndTeardownsInitialProductWithoutCachesGKRRelation {
        inputs: InitsOrTeardownsTimestampAndValue::Init,
        setup: [addr(10), addr(11)],
        address_high_bits: [0u32, 1u32],
        address_high_bits_shift: 0,
        output: addr(20),
    };

    let cs_meta = relation_metadata(&rel);
    let prover_nc = BatchedGKRKernel::<F, E>::num_challenges(&kernel);
    assert_eq!(
        cs_meta.num_challenges as usize, prover_nc,
        "InitsOrTeardownsInitialPair num_challenges mismatch"
    );
}

#[test]
fn num_challenges_lookup_from_vector_input_with_setup() {
    // LookupFromVectorInputWithSetup → LookupExtensionMinusMultiplicityByExtensionWithoutCachesGKRRelation
    // (num_challenges = 2). cs::num_challenges() panics on this variant.
    let vl = NoFieldVectorLookupRelation {
        columns: vec![NoFieldLinearRelation {
            linear_terms: vec![(1, GKRAddress::BaseLayerMemory(0))].into_boxed_slice(),
            constant: 0,
        }]
        .into_boxed_slice(),
        lookup_set_index: 0,
    };
    let rel = NoFieldGKRRelation::LookupFromVectorInputWithSetup {
        input: vl.clone(),
        setup: (addr(5), vec![addr(6)].into_boxed_slice()),
        output: [addr(30), addr(31)],
    };
    let kernel = LookupExtensionMinusMultiplicityByExtensionWithoutCachesGKRRelation {
        input: vl,
        setup: (addr(5), vec![addr(6)].into_boxed_slice()),
        outputs: [addr(30), addr(31)],
    };

    let cs_meta = relation_metadata(&rel);
    let prover_nc = BatchedGKRKernel::<F, E>::num_challenges(&kernel);
    assert_eq!(
        cs_meta.num_challenges as usize, prover_nc,
        "LookupFromVectorInputWithSetup num_challenges mismatch"
    );
}

#[test]
fn num_challenges_lookup_unbalanced_pair_with_vector_inputs() {
    // LookupUnbalancedPairWithVectorInputs → LookupRationalPairWithUnbalancedExtensionWithoutCachesGKRRelation
    // (num_challenges = 2). cs::num_challenges() panics on this variant.
    let vl = NoFieldVectorLookupRelation {
        columns: vec![NoFieldLinearRelation {
            linear_terms: vec![(1, GKRAddress::BaseLayerMemory(0))].into_boxed_slice(),
            constant: 0,
        }]
        .into_boxed_slice(),
        lookup_set_index: 0,
    };
    let rel = NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
        input: [addr(1), addr(2)],
        remainder: vl.clone(),
        output: [addr(40), addr(41)],
    };
    let kernel = LookupRationalPairWithUnbalancedExtensionWithoutCachesGKRRelation {
        inputs: [addr(1), addr(2)],
        remainder: vl,
        outputs: [addr(40), addr(41)],
    };

    let cs_meta = relation_metadata(&rel);
    let prover_nc = BatchedGKRKernel::<F, E>::num_challenges(&kernel);
    assert_eq!(
        cs_meta.num_challenges as usize, prover_nc,
        "LookupUnbalancedPairWithVectorInputs num_challenges mismatch"
    );
}

#[test]
fn num_challenges_lookup_unbalanced_pair_with_materialized_vector_inputs() {
    // LookupUnbalancedPairWithMaterializedVectorInputs → LookupRationalPairWithUnbalancedExtensionGKRRelation
    // (num_challenges = 2). cs::num_challenges() panics on this variant.
    // This variant also has get_inputs() implemented; domain check is in a separate test below.
    let rel = NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
        input: [addr(1), addr(2)],
        remainder: addr(3),
        output: [addr(50), addr(51)],
    };
    let kernel = LookupRationalPairWithUnbalancedExtensionGKRRelation::<F, E> {
        inputs: [addr(1), addr(2)],
        remainder: addr(3),
        outputs: [addr(50), addr(51)],
        lookup_additive_challenge: E::ONE,
        _marker: core::marker::PhantomData,
    };

    let cs_meta = relation_metadata(&rel);
    let prover_nc = BatchedGKRKernel::<F, E>::num_challenges(&kernel);
    assert_eq!(
        cs_meta.num_challenges as usize, prover_nc,
        "LookupUnbalancedPairWithMaterializedVectorInputs num_challenges mismatch"
    );
}

// ---------------------------------------------------------------------------
// (b) Per-operand domain cross-validation for GET_INPUTS_IMPLEMENTED kernels
//
// For each variant we read what domain each source address is assigned in the
// cs lowering (codegen_ir.rs lower_relation) and assert the kernel's GKRInputs
// agrees.
// ---------------------------------------------------------------------------

#[test]
fn domain_aggregate_lookup_rational_pair() {
    // AggregateLookupRationalPair → LookupPairGKRRelation
    // cs lowering: all four addresses are Domain::Ext
    let a0 = addr(0); let a1 = addr(1); let a2 = addr(2); let a3 = addr(3);
    let kernel = LookupPairGKRRelation {
        inputs: [[a0, a1], [a2, a3]],
        outputs: [addr(10), addr(11)],
    };
    let gi = BatchedGKRKernel::<F, E>::get_inputs(&kernel);
    // cs resolves input[0][0], [0][1], [1][0], [1][1] all as Ext
    let ext_addrs = [a0, a1, a2, a3];
    assert_domains_match(
        &[],
        &ext_addrs,
        &gi.inputs_in_base,
        &gi.inputs_in_extension,
        "AggregateLookupRationalPair",
    );
}

#[test]
fn domain_lookup_pair_from_materialized_base_inputs() {
    // LookupPairFromMaterializedBaseInputs → LookupBasePairGKRRelation
    // cs lowering: input[0], input[1] are Domain::Base
    let i0 = addr(0); let i1 = addr(1);
    let kernel = LookupBasePairGKRRelation::<F, E> {
        inputs: [i0, i1],
        outputs: [addr(10), addr(11)],
        lookup_additive_challenge: E::ONE,
        _marker: core::marker::PhantomData,
    };
    let gi = BatchedGKRKernel::<F, E>::get_inputs(&kernel);
    assert_domains_match(
        &[i0, i1],
        &[],
        &gi.inputs_in_base,
        &gi.inputs_in_extension,
        "LookupPairFromMaterializedBaseInputs",
    );
}

#[test]
fn domain_lookup_from_materialized_base_input_with_setup() {
    // LookupFromMaterializedBaseInputWithSetup → LookupBaseMinusMultiplicityByBaseGKRRelation
    // cs lowering: input, setup[0], setup[1] are all Domain::Base
    let i0 = addr(0); let s0 = addr(1); let s1 = addr(2);
    let kernel = LookupBaseMinusMultiplicityByBaseGKRRelation::<F, E> {
        input: i0,
        setup: [s0, s1],
        outputs: [addr(10), addr(11)],
        lookup_additive_challenge: E::ONE,
        _marker: core::marker::PhantomData,
    };
    let gi = BatchedGKRKernel::<F, E>::get_inputs(&kernel);
    assert_domains_match(
        &[i0, s0, s1],
        &[],
        &gi.inputs_in_base,
        &gi.inputs_in_extension,
        "LookupFromMaterializedBaseInputWithSetup",
    );
}

#[test]
fn domain_lookup_from_materialized_vector_input_with_setup() {
    // LookupFromMaterializedVectorInputWithSetup → LookupExtensionMinusMultiplicityByExtensionGKRRelation
    // cs lowering (line 628-631):
    //   input  → Domain::Ext
    //   setup[0] → Domain::Base
    //   setup[1] → Domain::Ext
    let i0 = addr(0); let s0 = addr(1); let s1 = addr(2);
    let kernel = LookupExtensionMinusMultiplicityByExtensionGKRRelation::<F, E> {
        input: i0,
        setup: [s0, s1],
        outputs: [addr(10), addr(11)],
        lookup_additive_challenge: E::ONE,
        _marker: core::marker::PhantomData,
    };
    let gi = BatchedGKRKernel::<F, E>::get_inputs(&kernel);
    // kernel: inputs_in_base=[setup[0]], inputs_in_ext=[input, setup[1]]
    assert_domains_match(
        &[s0],
        &[i0, s1],
        &gi.inputs_in_base,
        &gi.inputs_in_extension,
        "LookupFromMaterializedVectorInputWithSetup",
    );
}

#[test]
fn domain_lookup_unbalanced_pair_with_materialized_base_inputs() {
    // LookupUnbalancedPairWithMaterializedBaseInputs → LookupRationalPairWithUnbalancedBaseGKRRelation
    // cs lowering (line 604-608):
    //   input[0], input[1] → Domain::Ext
    //   remainder → Domain::Base
    let i0 = addr(0); let i1 = addr(1); let r = addr(2);
    let kernel = LookupRationalPairWithUnbalancedBaseGKRRelation::<F, E> {
        inputs: [i0, i1],
        remainder: r,
        outputs: [addr(10), addr(11)],
        lookup_additive_challenge: E::ONE,
        _marker: core::marker::PhantomData,
    };
    let gi = BatchedGKRKernel::<F, E>::get_inputs(&kernel);
    // kernel: inputs_in_base=[remainder], inputs_in_ext=[inputs[0], inputs[1]]
    assert_domains_match(
        &[r],
        &[i0, i1],
        &gi.inputs_in_base,
        &gi.inputs_in_extension,
        "LookupUnbalancedPairWithMaterializedBaseInputs",
    );
}

#[test]
fn domain_lookup_unbalanced_pair_with_materialized_vector_inputs() {
    // LookupUnbalancedPairWithMaterializedVectorInputs → LookupRationalPairWithUnbalancedExtensionGKRRelation
    // cs lowering (line 644-648):
    //   input[0], input[1] → Domain::Ext
    //   remainder → Domain::Ext
    // Also covered by num_challenges test (a) above.
    let i0 = addr(0); let i1 = addr(1); let r = addr(2);
    let kernel = LookupRationalPairWithUnbalancedExtensionGKRRelation::<F, E> {
        inputs: [i0, i1],
        remainder: r,
        outputs: [addr(10), addr(11)],
        lookup_additive_challenge: E::ONE,
        _marker: core::marker::PhantomData,
    };
    let gi = BatchedGKRKernel::<F, E>::get_inputs(&kernel);
    // kernel: inputs_in_ext=[inputs[0], inputs[1], remainder], inputs_in_base=[]
    assert_domains_match(
        &[],
        &[i0, i1, r],
        &gi.inputs_in_base,
        &gi.inputs_in_extension,
        "LookupUnbalancedPairWithMaterializedVectorInputs",
    );
}

#[test]
fn domain_lookup_with_cached_dens_and_setup() {
    // LookupWithCachedDensAndSetup → LookupBaseExtMinusBaseExtGKRRelation
    // cs lowering (line 567-571):
    //   input[0]  → Domain::Base  (nums[0])
    //   input[1]  → Domain::Ext   (dens[0])
    //   setup[0]  → Domain::Base  (nums[1])
    //   setup[1]  → Domain::Ext   (dens[1])
    let i0 = addr(0); let i1 = addr(1); let s0 = addr(2); let s1 = addr(3);
    let kernel = LookupBaseExtMinusBaseExtGKRRelation::<F, E> {
        nums: [i0, s0],
        dens: [i1, s1],
        outputs: [addr(10), addr(11)],
        lookup_additive_challenge: E::ONE,
        _marker: core::marker::PhantomData,
    };
    let gi = BatchedGKRKernel::<F, E>::get_inputs(&kernel);
    // kernel: inputs_in_base=nums=[i0, s0], inputs_in_ext=dens=[i1, s1]
    assert_domains_match(
        &[i0, s0],
        &[i1, s1],
        &gi.inputs_in_base,
        &gi.inputs_in_extension,
        "LookupWithCachedDensAndSetup",
    );
}

#[test]
fn domain_mask_into_identity_product() {
    // MaskIntoIdentityProduct → MaskIntoIdentityProductGKRRelation
    // cs lowering (line 544-549):
    //   mask  → Domain::Base
    //   input → Domain::Ext
    let mask = addr(0); let input = addr(1);
    let kernel = MaskIntoIdentityProductGKRRelation {
        input,
        mask,
        output: addr(10),
    };
    let gi = BatchedGKRKernel::<F, E>::get_inputs(&kernel);
    // kernel: inputs_in_base=[mask], inputs_in_ext=[input]
    assert_domains_match(
        &[mask],
        &[input],
        &gi.inputs_in_base,
        &gi.inputs_in_extension,
        "MaskIntoIdentityProduct",
    );
}
