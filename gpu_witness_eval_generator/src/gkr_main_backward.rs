use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs::File;
use std::path::Path;

use cs::definitions::gkr::{
    NoFieldLinearRelation, NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
    RamWordRepresentation,
};
use cs::definitions::{
    GKRAddress, MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRRelation,
    NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation,
    NoFieldSpecialMemoryContributionRelation,
};
use field::baby_bear::base::BabyBearField;

use crate::F;

const NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES: usize = 6;
const NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL: u32 = u32::MAX;
const BABY_BEAR_MINUS_ONE: u32 = BabyBearField::ORDER - 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeneratedMainBackwardFieldKind {
    Base,
    Extension,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeneratedMainBackwardKernelKind {
    BaseCopy,
    ExtCopy,
    Product,
    MaskIdentity,
    LookupPair,
    LookupBaseMinusMultiplicityByBase,
    LookupUnbalanced,
    LookupWithDensAndSetupExpressions,
    EnforceConstraintsMaxQuadratic,
    LinearBaseOutput,
    InitialGrandProductWithoutCaches,
    LookupPairFromBaseInputs,
}

impl GeneratedMainBackwardKernelKind {
    fn cpp_name(self) -> &'static str {
        match self {
            Self::BaseCopy => "GKR_MAIN_BASE_COPY",
            Self::ExtCopy => "GKR_MAIN_EXT_COPY",
            Self::Product => "GKR_MAIN_PRODUCT",
            Self::MaskIdentity => "GKR_MAIN_MASK_IDENTITY",
            Self::LookupPair => "GKR_MAIN_LOOKUP_PAIR",
            Self::LookupBaseMinusMultiplicityByBase => "GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY",
            Self::LookupUnbalanced => "GKR_MAIN_LOOKUP_UNBALANCED",
            Self::LookupWithDensAndSetupExpressions => {
                "GKR_MAIN_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS"
            }
            Self::EnforceConstraintsMaxQuadratic => "GKR_MAIN_ENFORCE_CONSTRAINTS",
            Self::LinearBaseOutput => "GKR_MAIN_LINEAR_BASE_OUTPUT",
            Self::InitialGrandProductWithoutCaches => {
                "GKR_MAIN_INITIAL_GRAND_PRODUCT_WITHOUT_CACHES"
            }
            Self::LookupPairFromBaseInputs => "GKR_MAIN_LOOKUP_PAIR_FROM_BASE_INPUTS",
        }
    }

    fn batch_challenge_count(self) -> usize {
        match self {
            Self::LookupPair
            | Self::LookupBaseMinusMultiplicityByBase
            | Self::LookupUnbalanced
            | Self::LookupWithDensAndSetupExpressions
            | Self::LookupPairFromBaseInputs => 2,
            Self::BaseCopy
            | Self::ExtCopy
            | Self::Product
            | Self::MaskIdentity
            | Self::EnforceConstraintsMaxQuadratic
            | Self::LinearBaseOutput
            | Self::InitialGrandProductWithoutCaches => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMainBackwardInputs {
    pub inputs_in_base: Vec<GKRAddress>,
    pub inputs_in_extension: Vec<GKRAddress>,
    pub outputs_in_base: Vec<GKRAddress>,
    pub outputs_in_extension: Vec<GKRAddress>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeneratedMainBackwardAuxiliaryChallengeSource {
    Zero,
    LookupAdditive,
}

impl GeneratedMainBackwardAuxiliaryChallengeSource {
    fn cpp_expr(self) -> &'static str {
        match self {
            Self::Zero => "E::ZERO()",
            Self::LookupAdditive => "challenges.lookup_additive_challenge",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeneratedMainBackwardChallengeSource {
    One,
    ExternalPermutationLinearization(usize),
    ExternalPermutationAdditive,
    LookupMultiplicative,
    LookupAdditive,
    ConstraintBatch,
}

impl GeneratedMainBackwardChallengeSource {
    fn cpp_name(self) -> String {
        match self {
            Self::One => "GKR_GENERATED_MAIN_SOURCE_ONE".to_owned(),
            Self::ExternalPermutationLinearization(idx) => {
                format!("GKR_GENERATED_MAIN_SOURCE_EXTERNAL_PERM_LINEARIZATION_{idx}")
            }
            Self::ExternalPermutationAdditive => {
                "GKR_GENERATED_MAIN_SOURCE_EXTERNAL_PERM_ADDITIVE".to_owned()
            }
            Self::LookupMultiplicative => {
                "GKR_GENERATED_MAIN_SOURCE_LOOKUP_MULTIPLICATIVE".to_owned()
            }
            Self::LookupAdditive => "GKR_GENERATED_MAIN_SOURCE_LOOKUP_ADDITIVE".to_owned(),
            Self::ConstraintBatch => "GKR_GENERATED_MAIN_SOURCE_CONSTRAINT_BATCH".to_owned(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMainBackwardChallengeTerm {
    pub coeff: u32,
    pub source: GeneratedMainBackwardChallengeSource,
    pub power: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMainBackwardConstraintQuadraticTerm {
    pub lhs: u32,
    pub rhs: u32,
    pub challenge_terms: Vec<GeneratedMainBackwardChallengeTerm>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMainBackwardConstraintLinearTerm {
    pub input: u32,
    pub challenge_terms: Vec<GeneratedMainBackwardChallengeTerm>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMainBackwardConstraintSpec {
    pub quadratic_terms: Vec<GeneratedMainBackwardConstraintQuadraticTerm>,
    pub linear_terms: Vec<GeneratedMainBackwardConstraintLinearTerm>,
    pub constant_terms: Vec<GeneratedMainBackwardChallengeTerm>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMainBackwardKernelSpec {
    pub kind: GeneratedMainBackwardKernelKind,
    pub inputs: GeneratedMainBackwardInputs,
    pub batch_challenge_offset: usize,
    pub batch_challenge_count: usize,
    pub auxiliary_challenge_source: GeneratedMainBackwardAuxiliaryChallengeSource,
    pub constraint: Option<GeneratedMainBackwardConstraintSpec>,
    pub round1_base_first_access: Vec<bool>,
    pub round1_extension_first_access: Vec<bool>,
    pub round2_base_first_access: Vec<bool>,
    pub round2_extension_first_access: Vec<bool>,
    pub round3_base_first_access: Vec<bool>,
    pub round3_extension_first_access: Vec<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMainBackwardLayerSpec {
    pub layer_idx: usize,
    pub kernels: Vec<GeneratedMainBackwardKernelSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMainBackwardSpec {
    pub layers: Vec<GeneratedMainBackwardLayerSpec>,
}

#[derive(Clone, Copy)]
enum GeneratedRoundKind {
    Round0,
    Round1Compact,
    Round2Compact,
    Round3Compact,
    Round3Explicit,
}

impl GeneratedRoundKind {
    fn function_name(self) -> &'static str {
        match self {
            Self::Round0 => "gkr_generated_add_sub_lui_auipc_mop_main_round0",
            Self::Round1Compact => "gkr_generated_add_sub_lui_auipc_mop_main_round1_compact",
            Self::Round2Compact => "gkr_generated_add_sub_lui_auipc_mop_main_round2_compact",
            Self::Round3Compact => "gkr_generated_add_sub_lui_auipc_mop_main_round3_compact",
            Self::Round3Explicit => "gkr_generated_add_sub_lui_auipc_mop_main_round3_explicit",
        }
    }

    fn static_ty(self) -> &'static str {
        match self {
            Self::Round0 => "gkr_main_round0_batch_static<E>",
            Self::Round1Compact => "gkr_main_round1_batch_static<E>",
            Self::Round2Compact => "gkr_main_round2_batch_static<E>",
            Self::Round3Compact | Self::Round3Explicit => "gkr_main_round3_batch_static<E>",
        }
    }

    fn runtime_ty(self) -> &'static str {
        match self {
            Self::Round0 => "gkr_main_round0_batch_runtime<E>",
            Self::Round1Compact => "gkr_main_round1_batch_runtime<E>",
            Self::Round2Compact => "gkr_main_round2_batch_runtime<E>",
            Self::Round3Compact | Self::Round3Explicit => "gkr_main_round3_batch_runtime<E>",
        }
    }

    fn value_call(self) -> &'static str {
        match self {
            Self::Round0 => "gkr_main_round0_values",
            Self::Round1Compact => "gkr_main_round1_values<E, false>",
            Self::Round2Compact => "gkr_main_round2_values<E, false>",
            Self::Round3Compact => "gkr_main_round3_values<E, false>",
            Self::Round3Explicit => "gkr_main_round3_values<E, true>",
        }
    }

    fn base_descriptor_ty(self) -> &'static str {
        match self {
            Self::Round0 => "gkr_base_initial_source<bf>",
            Self::Round1Compact => "gkr_base_after_one_source<bf, E>",
            Self::Round2Compact => "gkr_base_after_two_source<bf, E>",
            Self::Round3Compact | Self::Round3Explicit => "gkr_ext_continuing_source<E>",
        }
    }

    fn extension_descriptor_ty(self) -> &'static str {
        match self {
            Self::Round0 => "gkr_ext_initial_source<E>",
            Self::Round1Compact
            | Self::Round2Compact
            | Self::Round3Compact
            | Self::Round3Explicit => "gkr_ext_continuing_source<E>",
        }
    }
}

fn remap_constraint_input(
    mapping: &mut BTreeMap<GKRAddress, usize>,
    inputs: &mut Vec<GKRAddress>,
    address: GKRAddress,
) -> usize {
    match address {
        GKRAddress::ScratchSpace(..) => {
            panic!("scratch-space addresses are not valid constraint inputs")
        }
        _ => {}
    }
    if let Some(idx) = mapping.get(&address).copied() {
        idx
    } else {
        let idx = mapping.len();
        mapping.insert(address, idx);
        inputs.push(address);
        idx
    }
}

fn constant_term(coeff: u32) -> GeneratedMainBackwardChallengeTerm {
    GeneratedMainBackwardChallengeTerm {
        coeff,
        source: GeneratedMainBackwardChallengeSource::One,
        power: 0,
    }
}

fn challenge_term(
    coeff: u32,
    source: GeneratedMainBackwardChallengeSource,
    power: u32,
) -> GeneratedMainBackwardChallengeTerm {
    GeneratedMainBackwardChallengeTerm {
        coeff,
        source,
        power,
    }
}

fn merge_terms(
    dst: &mut BTreeMap<GKRAddress, Vec<GeneratedMainBackwardChallengeTerm>>,
    address: GKRAddress,
    term: GeneratedMainBackwardChallengeTerm,
) {
    dst.entry(address).or_default().push(term);
}

fn memory_query_as_flattened_relation_template(
    rel: &NoFieldSpecialMemoryContributionRelation,
) -> (
    BTreeMap<GKRAddress, Vec<GeneratedMainBackwardChallengeTerm>>,
    Vec<GeneratedMainBackwardChallengeTerm>,
) {
    let mut result = BTreeMap::new();
    let mut constant_terms = vec![challenge_term(
        1,
        GeneratedMainBackwardChallengeSource::ExternalPermutationAdditive,
        1,
    )];

    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            if c != 0 {
                constant_terms.push(constant_term(c));
            }
        }
        CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(offset),
                constant_term(1),
            );
        }
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(offset),
                constant_term(BABY_BEAR_MINUS_ONE),
            );
            constant_terms.push(constant_term(1));
        }
    }

    match &rel.address {
        CompiledAddressStrict::ConstantU16(c) => {
            if *c != 0 {
                constant_terms.push(challenge_term(
                    *c as u32,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    ),
                    1,
                ));
            }
        }
        CompiledAddressStrict::Constant(c) => {
            if *c != 0 {
                constant_terms.push(challenge_term(
                    *c,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    ),
                    1,
                ));
            }
        }
        CompiledAddressStrict::U16Space(offset) => {
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(*offset),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    ),
                    1,
                ),
            );
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(*low),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    ),
                    1,
                ),
            );
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(*high),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
                    ),
                    1,
                ),
            );
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            if let Some((c, offset)) = *low_dynamic_offset {
                merge_terms(
                    &mut result,
                    GKRAddress::BaseLayerMemory(offset),
                    challenge_term(
                        c as u32,
                        GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                            MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                        ),
                        1,
                    ),
                );
            }
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(*low_base),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    ),
                    1,
                ),
            );
            if *low_offset != 0 {
                constant_terms.push(challenge_term(
                    *low_offset,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    ),
                    1,
                ));
            }
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(*high),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
                    ),
                    1,
                ),
            );
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            panic!("U32SpaceGeneric is unsupported in generated main backward lowering");
        }
    }

    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal([low, high]) => {
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(low),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                    ),
                    1,
                ),
            );
            if rel.timestamp_offset != 0 {
                constant_terms.push(challenge_term(
                    rel.timestamp_offset,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                    ),
                    1,
                ));
            }
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(high),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                    ),
                    1,
                ),
            );
        }
    }

    match rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs([low, high]) => {
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(low),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    ),
                    1,
                ),
            );
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(high),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    ),
                    1,
                ),
            );
        }
        RamWordRepresentation::U8Limbs([b0, b1, b2, b3]) => {
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(b0),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    ),
                    1,
                ),
            );
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(b1),
                challenge_term(
                    1 << 8,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    ),
                    1,
                ),
            );
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(b2),
                challenge_term(
                    1,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    ),
                    1,
                ),
            );
            merge_terms(
                &mut result,
                GKRAddress::BaseLayerMemory(b3),
                challenge_term(
                    1 << 8,
                    GeneratedMainBackwardChallengeSource::ExternalPermutationLinearization(
                        MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    ),
                    1,
                ),
            );
        }
    }

    (result, constant_terms)
}

fn single_column_lookup_as_flattened_relation_template(
    rel: &NoFieldSingleColumnLookupRelation,
) -> (
    BTreeMap<GKRAddress, Vec<GeneratedMainBackwardChallengeTerm>>,
    Vec<GeneratedMainBackwardChallengeTerm>,
) {
    let mut result = BTreeMap::new();
    let mut constant_terms = vec![challenge_term(
        1,
        GeneratedMainBackwardChallengeSource::LookupAdditive,
        1,
    )];

    if rel.input.constant != 0 {
        constant_terms.push(constant_term(rel.input.constant));
    }

    for (coeff, address) in rel.input.linear_terms.iter() {
        merge_terms(&mut result, *address, constant_term(*coeff));
    }

    (result, constant_terms)
}

fn vector_lookup_as_flattened_relation_template(
    rel: &NoFieldVectorLookupRelation,
) -> (
    BTreeMap<GKRAddress, Vec<GeneratedMainBackwardChallengeTerm>>,
    Vec<GeneratedMainBackwardChallengeTerm>,
) {
    let mut result = BTreeMap::new();
    let mut constant_terms = vec![challenge_term(
        1,
        GeneratedMainBackwardChallengeSource::LookupAdditive,
        1,
    )];

    for (idx, column) in rel.columns.iter().enumerate() {
        let power = idx as u32;
        for (coeff, address) in column.linear_terms.iter() {
            merge_terms(
                &mut result,
                *address,
                challenge_term(
                    *coeff,
                    GeneratedMainBackwardChallengeSource::LookupMultiplicative,
                    power,
                ),
            );
        }
        if column.constant != 0 {
            constant_terms.push(challenge_term(
                column.constant,
                GeneratedMainBackwardChallengeSource::LookupMultiplicative,
                power,
            ));
        }
    }

    (result, constant_terms)
}

fn flatten_lookup_setup_relation_template(
    setup: &[GKRAddress],
) -> (
    BTreeMap<GKRAddress, Vec<GeneratedMainBackwardChallengeTerm>>,
    Vec<GeneratedMainBackwardChallengeTerm>,
) {
    let mut terms = BTreeMap::new();
    for (idx, address) in setup.iter().copied().enumerate() {
        merge_terms(
            &mut terms,
            address,
            challenge_term(
                1,
                GeneratedMainBackwardChallengeSource::LookupMultiplicative,
                idx as u32,
            ),
        );
    }
    (
        terms,
        vec![challenge_term(
            1,
            GeneratedMainBackwardChallengeSource::LookupAdditive,
            1,
        )],
    )
}

fn collect_linear_form_inputs(
    forms: &[&BTreeMap<GKRAddress, Vec<GeneratedMainBackwardChallengeTerm>>],
) -> (BTreeMap<GKRAddress, usize>, Vec<GKRAddress>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    for terms in forms.iter().copied() {
        for address in terms.keys().copied() {
            remap_constraint_input(&mut mapping, &mut inputs, address);
        }
    }
    (mapping, inputs)
}

fn encode_linear_form_as_quadratic_terms(
    mapping: &BTreeMap<GKRAddress, usize>,
    terms: &BTreeMap<GKRAddress, Vec<GeneratedMainBackwardChallengeTerm>>,
    constant_terms: &[GeneratedMainBackwardChallengeTerm],
) -> Vec<GeneratedMainBackwardConstraintQuadraticTerm> {
    let mut encoded = terms
        .iter()
        .map(
            |(address, challenge_terms)| GeneratedMainBackwardConstraintQuadraticTerm {
                lhs: mapping[address] as u32,
                rhs: 0,
                challenge_terms: challenge_terms.clone(),
            },
        )
        .collect::<Vec<_>>();
    if !constant_terms.is_empty() {
        encoded.push(GeneratedMainBackwardConstraintQuadraticTerm {
            lhs: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            rhs: 0,
            challenge_terms: constant_terms.to_vec(),
        });
    }
    encoded
}

fn encode_linear_form_as_linear_terms(
    mapping: &BTreeMap<GKRAddress, usize>,
    terms: &BTreeMap<GKRAddress, Vec<GeneratedMainBackwardChallengeTerm>>,
    constant_terms: &[GeneratedMainBackwardChallengeTerm],
) -> Vec<GeneratedMainBackwardConstraintLinearTerm> {
    let mut encoded = terms
        .iter()
        .map(
            |(address, challenge_terms)| GeneratedMainBackwardConstraintLinearTerm {
                input: mapping[address] as u32,
                challenge_terms: challenge_terms.clone(),
            },
        )
        .collect::<Vec<_>>();
    if !constant_terms.is_empty() {
        encoded.push(GeneratedMainBackwardConstraintLinearTerm {
            input: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            challenge_terms: constant_terms.to_vec(),
        });
    }
    encoded
}

fn build_single_max_quadratic_constraint_inputs_and_constraint(
    relation: &NoFieldMaxQuadraticGKRRelation,
) -> (
    GeneratedMainBackwardInputs,
    GeneratedMainBackwardConstraintSpec,
) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut quadratic_terms = Vec::new();
    let mut linear_terms = Vec::new();

    for (lhs, rhs_terms) in relation.quadratic_terms.iter() {
        let lhs_idx = remap_constraint_input(&mut mapping, &mut inputs, *lhs);
        for (coeff, rhs) in rhs_terms.iter() {
            let rhs_idx = if *lhs == *rhs {
                lhs_idx
            } else {
                remap_constraint_input(&mut mapping, &mut inputs, *rhs)
            };
            quadratic_terms.push(GeneratedMainBackwardConstraintQuadraticTerm {
                lhs: lhs_idx as u32,
                rhs: rhs_idx as u32,
                challenge_terms: vec![constant_term(*coeff)],
            });
        }
    }

    for (coeff, input) in relation.linear_terms.iter() {
        let input_idx = remap_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(GeneratedMainBackwardConstraintLinearTerm {
            input: input_idx as u32,
            challenge_terms: vec![constant_term(*coeff)],
        });
    }

    (
        GeneratedMainBackwardInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        },
        GeneratedMainBackwardConstraintSpec {
            quadratic_terms,
            linear_terms,
            constant_terms: if relation.constant == 0 {
                Vec::new()
            } else {
                vec![constant_term(relation.constant)]
            },
        },
    )
}

fn build_constraints_max_quadratic_inputs_and_constraint(
    relation: &NoFieldMaxQuadraticConstraintsGKRRelation,
) -> (
    GeneratedMainBackwardInputs,
    GeneratedMainBackwardConstraintSpec,
) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut quadratic_terms = Vec::new();
    let mut linear_terms = Vec::new();

    for ((lhs, rhs), challenge_terms) in relation.quadratic_terms.iter() {
        let lhs_idx = remap_constraint_input(&mut mapping, &mut inputs, *lhs);
        let rhs_idx = if *lhs == *rhs {
            lhs_idx
        } else {
            remap_constraint_input(&mut mapping, &mut inputs, *rhs)
        };
        quadratic_terms.push(GeneratedMainBackwardConstraintQuadraticTerm {
            lhs: lhs_idx as u32,
            rhs: rhs_idx as u32,
            challenge_terms: challenge_terms
                .iter()
                .map(|(coeff, power)| {
                    challenge_term(
                        *coeff,
                        GeneratedMainBackwardChallengeSource::ConstraintBatch,
                        *power as u32,
                    )
                })
                .collect(),
        });
    }

    for (input, challenge_terms) in relation.linear_terms.iter() {
        let input_idx = remap_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(GeneratedMainBackwardConstraintLinearTerm {
            input: input_idx as u32,
            challenge_terms: challenge_terms
                .iter()
                .map(|(coeff, power)| {
                    challenge_term(
                        *coeff,
                        GeneratedMainBackwardChallengeSource::ConstraintBatch,
                        *power as u32,
                    )
                })
                .collect(),
        });
    }

    (
        GeneratedMainBackwardInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        },
        GeneratedMainBackwardConstraintSpec {
            quadratic_terms,
            linear_terms,
            constant_terms: relation
                .constants
                .iter()
                .map(|(coeff, power)| {
                    challenge_term(
                        *coeff,
                        GeneratedMainBackwardChallengeSource::ConstraintBatch,
                        *power as u32,
                    )
                })
                .collect(),
        },
    )
}

fn build_linear_base_kernel_inputs_and_constraint(
    relation: &NoFieldLinearRelation,
    output: GKRAddress,
) -> (
    GeneratedMainBackwardInputs,
    GeneratedMainBackwardConstraintSpec,
) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut linear_terms = Vec::new();

    for (coeff, input) in relation.linear_terms.iter() {
        let input_idx = remap_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(GeneratedMainBackwardConstraintLinearTerm {
            input: input_idx as u32,
            challenge_terms: vec![constant_term(*coeff)],
        });
    }

    (
        GeneratedMainBackwardInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: vec![output],
            outputs_in_extension: Vec::new(),
        },
        GeneratedMainBackwardConstraintSpec {
            quadratic_terms: Vec::new(),
            linear_terms,
            constant_terms: if relation.constant == 0 {
                Vec::new()
            } else {
                vec![constant_term(relation.constant)]
            },
        },
    )
}

fn build_initial_grand_product_without_caches_inputs_and_constraint(
    input: &[NoFieldSpecialMemoryContributionRelation; 2],
    output: GKRAddress,
) -> (
    GeneratedMainBackwardInputs,
    GeneratedMainBackwardConstraintSpec,
) {
    let (lhs_terms, lhs_constant_terms) = memory_query_as_flattened_relation_template(&input[0]);
    let (rhs_terms, rhs_constant_terms) = memory_query_as_flattened_relation_template(&input[1]);
    let (mapping, inputs) = collect_linear_form_inputs(&[&lhs_terms, &rhs_terms]);

    (
        GeneratedMainBackwardInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![output],
        },
        GeneratedMainBackwardConstraintSpec {
            quadratic_terms: encode_linear_form_as_quadratic_terms(
                &mapping,
                &lhs_terms,
                &lhs_constant_terms,
            ),
            linear_terms: encode_linear_form_as_linear_terms(
                &mapping,
                &rhs_terms,
                &rhs_constant_terms,
            ),
            constant_terms: Vec::new(),
        },
    )
}

fn build_lookup_pair_from_base_inputs_inputs_and_constraint(
    input: &[NoFieldSingleColumnLookupRelation; 2],
    output: [GKRAddress; 2],
) -> (
    GeneratedMainBackwardInputs,
    GeneratedMainBackwardConstraintSpec,
) {
    let (lhs_terms, lhs_constant_terms) =
        single_column_lookup_as_flattened_relation_template(&input[0]);
    let (rhs_terms, rhs_constant_terms) =
        single_column_lookup_as_flattened_relation_template(&input[1]);
    let (mapping, inputs) = collect_linear_form_inputs(&[&lhs_terms, &rhs_terms]);

    (
        GeneratedMainBackwardInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        GeneratedMainBackwardConstraintSpec {
            quadratic_terms: encode_linear_form_as_quadratic_terms(
                &mapping,
                &lhs_terms,
                &lhs_constant_terms,
            ),
            linear_terms: encode_linear_form_as_linear_terms(
                &mapping,
                &rhs_terms,
                &rhs_constant_terms,
            ),
            constant_terms: Vec::new(),
        },
    )
}

fn build_lookup_with_dens_and_setup_expressions_inputs_and_constraint(
    input: &(GKRAddress, NoFieldVectorLookupRelation),
    setup: &(GKRAddress, Box<[GKRAddress]>),
    output: [GKRAddress; 2],
) -> (
    GeneratedMainBackwardInputs,
    GeneratedMainBackwardConstraintSpec,
) {
    let (input_terms, input_constant_terms) =
        vector_lookup_as_flattened_relation_template(&input.1);
    let (setup_terms, setup_constant_terms) =
        flatten_lookup_setup_relation_template(setup.1.as_ref());
    let (tail_mapping, tail_inputs) = collect_linear_form_inputs(&[&input_terms, &setup_terms]);
    let inputs = std::iter::once(input.0)
        .chain(std::iter::once(setup.0))
        .chain(tail_inputs.iter().copied())
        .collect::<Vec<_>>();

    (
        GeneratedMainBackwardInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        GeneratedMainBackwardConstraintSpec {
            quadratic_terms: encode_linear_form_as_quadratic_terms(
                &tail_mapping,
                &input_terms,
                &input_constant_terms,
            ),
            linear_terms: encode_linear_form_as_linear_terms(
                &tail_mapping,
                &setup_terms,
                &setup_constant_terms,
            ),
            constant_terms: Vec::new(),
        },
    )
}

fn classify_known_field_kind(
    field_kinds: &BTreeMap<GKRAddress, GeneratedMainBackwardFieldKind>,
    address: GKRAddress,
) -> Option<GeneratedMainBackwardFieldKind> {
    field_kinds
        .get(&address)
        .copied()
        .or_else(|| match address {
            GKRAddress::BaseLayerWitness(..)
            | GKRAddress::BaseLayerMemory(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => Some(GeneratedMainBackwardFieldKind::Base),
            GKRAddress::InnerLayer { .. }
            | GKRAddress::Cached { .. }
            | GKRAddress::ScratchSpace(..) => None,
        })
}

fn register_outputs(
    field_kinds: &mut BTreeMap<GKRAddress, GeneratedMainBackwardFieldKind>,
    inputs: &GeneratedMainBackwardInputs,
) -> Result<(), String> {
    for address in inputs.outputs_in_base.iter().copied() {
        if let Some(existing) = classify_known_field_kind(field_kinds, address) {
            if existing != GeneratedMainBackwardFieldKind::Base {
                return Err(format!(
                    "conflicting field-kind classification for {address:?}"
                ));
            }
        }
        field_kinds.insert(address, GeneratedMainBackwardFieldKind::Base);
    }
    for address in inputs.outputs_in_extension.iter().copied() {
        if let Some(existing) = classify_known_field_kind(field_kinds, address) {
            if existing != GeneratedMainBackwardFieldKind::Extension {
                return Err(format!(
                    "conflicting field-kind classification for {address:?}"
                ));
            }
        }
        field_kinds.insert(address, GeneratedMainBackwardFieldKind::Extension);
    }
    Ok(())
}

fn assign_first_access_flags(kernels: &mut [GeneratedMainBackwardKernelSpec]) {
    fn compute(
        kernels: &mut [GeneratedMainBackwardKernelSpec],
        pick_base: impl Fn(&mut GeneratedMainBackwardKernelSpec) -> (&[GKRAddress], &mut Vec<bool>),
        pick_ext: impl Fn(&mut GeneratedMainBackwardKernelSpec) -> (&[GKRAddress], &mut Vec<bool>),
    ) {
        let mut seen_base = BTreeMap::<GKRAddress, ()>::new();
        let mut seen_ext = BTreeMap::<GKRAddress, ()>::new();
        for kernel in kernels.iter_mut() {
            let (base_inputs, base_flags) = pick_base(kernel);
            base_flags.clear();
            base_flags.extend(
                base_inputs
                    .iter()
                    .map(|address| seen_base.insert(*address, ()).is_none()),
            );
            let (ext_inputs, ext_flags) = pick_ext(kernel);
            ext_flags.clear();
            ext_flags.extend(
                ext_inputs
                    .iter()
                    .map(|address| seen_ext.insert(*address, ()).is_none()),
            );
        }
    }

    compute(
        kernels,
        |kernel| {
            (
                &kernel.inputs.inputs_in_base,
                &mut kernel.round1_base_first_access,
            )
        },
        |kernel| {
            (
                &kernel.inputs.inputs_in_extension,
                &mut kernel.round1_extension_first_access,
            )
        },
    );
    compute(
        kernels,
        |kernel| {
            (
                &kernel.inputs.inputs_in_base,
                &mut kernel.round2_base_first_access,
            )
        },
        |kernel| {
            (
                &kernel.inputs.inputs_in_extension,
                &mut kernel.round2_extension_first_access,
            )
        },
    );
    compute(
        kernels,
        |kernel| {
            (
                &kernel.inputs.inputs_in_base,
                &mut kernel.round3_base_first_access,
            )
        },
        |kernel| {
            (
                &kernel.inputs.inputs_in_extension,
                &mut kernel.round3_extension_first_access,
            )
        },
    );
}

fn lower_layer(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    field_kinds: &mut BTreeMap<GKRAddress, GeneratedMainBackwardFieldKind>,
) -> Result<GeneratedMainBackwardLayerSpec, String> {
    let mut kernels = Vec::new();
    let mut next_batch_challenge_offset = 0usize;

    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let relation = &gate.enforced_relation;
        let (kind, inputs, auxiliary_challenge_source, constraint) = match relation {
            NoFieldGKRRelation::Copy { input, output } => {
                let field_kind = classify_known_field_kind(field_kinds, *input)
                    .ok_or_else(|| format!("missing field-kind classification for copy input {input:?} in layer {layer_idx}"))?;
                let kind = match field_kind {
                    GeneratedMainBackwardFieldKind::Base => {
                        GeneratedMainBackwardKernelKind::BaseCopy
                    }
                    GeneratedMainBackwardFieldKind::Extension => {
                        GeneratedMainBackwardKernelKind::ExtCopy
                    }
                };
                let inputs = match field_kind {
                    GeneratedMainBackwardFieldKind::Base => GeneratedMainBackwardInputs {
                        inputs_in_base: vec![*input],
                        inputs_in_extension: Vec::new(),
                        outputs_in_base: vec![*output],
                        outputs_in_extension: Vec::new(),
                    },
                    GeneratedMainBackwardFieldKind::Extension => GeneratedMainBackwardInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: vec![*input],
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: vec![*output],
                    },
                };
                (
                    kind,
                    inputs,
                    GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                    None,
                )
            }
            NoFieldGKRRelation::TrivialProduct { input, output }
            | NoFieldGKRRelation::InitialGrandProductFromCaches { input, output } => (
                GeneratedMainBackwardKernelKind::Product,
                GeneratedMainBackwardInputs {
                    inputs_in_base: Vec::new(),
                    inputs_in_extension: input.to_vec(),
                    outputs_in_base: Vec::new(),
                    outputs_in_extension: vec![*output],
                },
                GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                None,
            ),
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                let (inputs, constraint) =
                    build_initial_grand_product_without_caches_inputs_and_constraint(
                        input, *output,
                    );
                (
                    GeneratedMainBackwardKernelKind::InitialGrandProductWithoutCaches,
                    inputs,
                    GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                    Some(constraint),
                )
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => (
                GeneratedMainBackwardKernelKind::MaskIdentity,
                GeneratedMainBackwardInputs {
                    inputs_in_base: vec![*mask],
                    inputs_in_extension: vec![*input],
                    outputs_in_base: Vec::new(),
                    outputs_in_extension: vec![*output],
                },
                GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                None,
            ),
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => (
                GeneratedMainBackwardKernelKind::LookupPair,
                GeneratedMainBackwardInputs {
                    inputs_in_base: Vec::new(),
                    inputs_in_extension: [input[0][0], input[0][1], input[1][0], input[1][1]]
                        .to_vec(),
                    outputs_in_base: Vec::new(),
                    outputs_in_extension: output.to_vec(),
                },
                GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                None,
            ),
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => (
                GeneratedMainBackwardKernelKind::LookupBaseMinusMultiplicityByBase,
                GeneratedMainBackwardInputs {
                    inputs_in_base: vec![*input, setup[0], setup[1]],
                    inputs_in_extension: Vec::new(),
                    outputs_in_base: Vec::new(),
                    outputs_in_extension: output.to_vec(),
                },
                GeneratedMainBackwardAuxiliaryChallengeSource::LookupAdditive,
                None,
            ),
            NoFieldGKRRelation::LookupPairFromBaseInputs { input, output, .. } => {
                let (inputs, constraint) =
                    build_lookup_pair_from_base_inputs_inputs_and_constraint(input, *output);
                (
                    GeneratedMainBackwardKernelKind::LookupPairFromBaseInputs,
                    inputs,
                    GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                    Some(constraint),
                )
            }
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint) =
                    build_lookup_with_dens_and_setup_expressions_inputs_and_constraint(
                        input, setup, *output,
                    );
                (
                    GeneratedMainBackwardKernelKind::LookupWithDensAndSetupExpressions,
                    inputs,
                    GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                    Some(constraint),
                )
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => (
                GeneratedMainBackwardKernelKind::LookupUnbalanced,
                GeneratedMainBackwardInputs {
                    inputs_in_base: vec![*remainder],
                    inputs_in_extension: input.to_vec(),
                    outputs_in_base: Vec::new(),
                    outputs_in_extension: output.to_vec(),
                },
                GeneratedMainBackwardAuxiliaryChallengeSource::LookupAdditive,
                None,
            ),
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input } => {
                let (inputs, constraint) =
                    build_single_max_quadratic_constraint_inputs_and_constraint(input);
                (
                    GeneratedMainBackwardKernelKind::EnforceConstraintsMaxQuadratic,
                    inputs,
                    GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                    Some(constraint),
                )
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let (inputs, constraint) =
                    build_constraints_max_quadratic_inputs_and_constraint(input);
                (
                    GeneratedMainBackwardKernelKind::EnforceConstraintsMaxQuadratic,
                    inputs,
                    GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                    Some(constraint),
                )
            }
            NoFieldGKRRelation::MaterializeSingleLookupInput { input, output, .. } => {
                let (inputs, constraint) =
                    build_linear_base_kernel_inputs_and_constraint(&input.input, *output);
                (
                    GeneratedMainBackwardKernelKind::LinearBaseOutput,
                    inputs,
                    GeneratedMainBackwardAuxiliaryChallengeSource::Zero,
                    Some(constraint),
                )
            }
            other => {
                return Err(format!(
                    "unsupported relation in generated add_sub_lui_auipc_mop main backward lowering: {other:?}"
                ));
            }
        };

        let batch_challenge_count = kind.batch_challenge_count();
        let batch_challenge_offset = next_batch_challenge_offset;
        next_batch_challenge_offset += batch_challenge_count;

        register_outputs(field_kinds, &inputs)?;
        kernels.push(GeneratedMainBackwardKernelSpec {
            kind,
            inputs,
            batch_challenge_offset,
            batch_challenge_count,
            auxiliary_challenge_source,
            constraint,
            round1_base_first_access: Vec::new(),
            round1_extension_first_access: Vec::new(),
            round2_base_first_access: Vec::new(),
            round2_extension_first_access: Vec::new(),
            round3_base_first_access: Vec::new(),
            round3_extension_first_access: Vec::new(),
        });
    }

    assign_first_access_flags(&mut kernels);
    Ok(GeneratedMainBackwardLayerSpec { layer_idx, kernels })
}

pub fn lower_add_sub_lui_auipc_mop_main_backward(
    circuit: &GKRCircuitArtifact<F>,
) -> Result<GeneratedMainBackwardSpec, String> {
    let mut field_kinds = BTreeMap::new();
    let mut layers = Vec::with_capacity(circuit.layers.len());
    for (layer_idx, layer) in circuit.layers.iter().enumerate() {
        layers.push(lower_layer(layer, layer_idx, &mut field_kinds)?);
    }
    Ok(GeneratedMainBackwardSpec { layers })
}

fn emit_local_terms_array(
    out: &mut String,
    name: &str,
    terms: &[GeneratedMainBackwardChallengeTerm],
) {
    let _ = writeln!(
        out,
        "      const gkr_generated_main_challenge_term {name}[{}] = {{",
        terms.len()
    );
    for term in terms.iter() {
        let _ = writeln!(
            out,
            "    {{{}, {}, {}, 0}},",
            term.coeff,
            term.source.cpp_name(),
            term.power
        );
    }
    let _ = writeln!(out, "}};");
}

fn emit_descriptor_copy_block(
    out: &mut String,
    ty: &str,
    src_name: &str,
    local_name: &str,
    result_name: &str,
    first_access: &[bool],
) {
    if first_access.is_empty() {
        let _ = writeln!(out, "      const auto *{result_name} = {src_name};");
        return;
    }
    let _ = writeln!(out, "      {ty} {local_name}[{}];", first_access.len());
    for (idx, first_access) in first_access.iter().enumerate() {
        let _ = writeln!(out, "      {local_name}[{idx}] = {src_name}[{idx}];");
        let _ = writeln!(
            out,
            "      {local_name}[{idx}].first_access = {};",
            if *first_access { "true" } else { "false" }
        );
    }
    let _ = writeln!(out, "      const auto *{result_name} = {local_name};");
}

fn emit_constraint_block(
    out: &mut String,
    layer_idx: usize,
    kernel_idx: usize,
    constraint: Option<&GeneratedMainBackwardConstraintSpec>,
) {
    let Some(constraint) = constraint else {
        let _ = writeln!(
            out,
            "      const gkr_main_constraint_quadratic_term<E> *quadratic_terms = nullptr;"
        );
        let _ = writeln!(out, "      const unsigned quadratic_terms_count = 0;");
        let _ = writeln!(
            out,
            "      const gkr_main_constraint_linear_term<E> *linear_terms = nullptr;"
        );
        let _ = writeln!(out, "      const unsigned linear_terms_count = 0;");
        let _ = writeln!(out, "      const E constant_offset = E::ZERO();");
        return;
    };

    if constraint.quadratic_terms.is_empty() {
        let _ = writeln!(
            out,
            "      const gkr_main_constraint_quadratic_term<E> *quadratic_terms = nullptr;"
        );
        let _ = writeln!(out, "      const unsigned quadratic_terms_count = 0;");
    } else {
        for (term_idx, quadratic) in constraint.quadratic_terms.iter().enumerate() {
            let name = format!("quadratic_{}_{}_{}_terms", layer_idx, kernel_idx, term_idx);
            emit_local_terms_array(out, &name, &quadratic.challenge_terms);
        }
        let _ = writeln!(
            out,
            "      gkr_main_constraint_quadratic_term<E> quadratic_terms_storage[{}];",
            constraint.quadratic_terms.len()
        );
        for (term_idx, quadratic) in constraint.quadratic_terms.iter().enumerate() {
            let name = format!("quadratic_{}_{}_{}_terms", layer_idx, kernel_idx, term_idx);
            let _ = writeln!(
                out,
                "      quadratic_terms_storage[{term_idx}] = {{{}, {}, gkr_generated_main_eval_terms({}, {}, challenges)}};",
                quadratic.lhs,
                quadratic.rhs,
                name,
                quadratic.challenge_terms.len()
            );
        }
        let _ = writeln!(
            out,
            "      const auto *quadratic_terms = quadratic_terms_storage;"
        );
        let _ = writeln!(
            out,
            "      const unsigned quadratic_terms_count = {};",
            constraint.quadratic_terms.len()
        );
    }

    if constraint.linear_terms.is_empty() {
        let _ = writeln!(
            out,
            "      const gkr_main_constraint_linear_term<E> *linear_terms = nullptr;"
        );
        let _ = writeln!(out, "      const unsigned linear_terms_count = 0;");
    } else {
        for (term_idx, linear) in constraint.linear_terms.iter().enumerate() {
            let name = format!("linear_{}_{}_{}_terms", layer_idx, kernel_idx, term_idx);
            emit_local_terms_array(out, &name, &linear.challenge_terms);
        }
        let _ = writeln!(
            out,
            "      gkr_main_constraint_linear_term<E> linear_terms_storage[{}];",
            constraint.linear_terms.len()
        );
        for (term_idx, linear) in constraint.linear_terms.iter().enumerate() {
            let name = format!("linear_{}_{}_{}_terms", layer_idx, kernel_idx, term_idx);
            let _ = writeln!(
                out,
                "      linear_terms_storage[{term_idx}] = {{{}, gkr_generated_main_eval_terms({}, {}, challenges)}};",
                linear.input,
                name,
                linear.challenge_terms.len()
            );
        }
        let _ = writeln!(
            out,
            "      const auto *linear_terms = linear_terms_storage;"
        );
        let _ = writeln!(
            out,
            "      const unsigned linear_terms_count = {};",
            constraint.linear_terms.len()
        );
    }

    if constraint.constant_terms.is_empty() {
        let _ = writeln!(out, "      const E constant_offset = E::ZERO();");
    } else {
        let name = format!("constant_{}_{}_terms", layer_idx, kernel_idx);
        emit_local_terms_array(out, &name, &constraint.constant_terms);
        let _ = writeln!(
            out,
            "      const E constant_offset = gkr_generated_main_eval_terms({}, {}, challenges);",
            name,
            constraint.constant_terms.len()
        );
    }
}

fn emit_kernel_block(
    out: &mut String,
    layer_idx: usize,
    kernel_idx: usize,
    kernel: &GeneratedMainBackwardKernelSpec,
    round: GeneratedRoundKind,
) {
    let _ = writeln!(out, "    {{");
    let _ = writeln!(
        out,
        "      const auto &record = batch_static.records[{kernel_idx}];"
    );
    let _ = writeln!(
        out,
        "      const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);"
    );

    match round {
        GeneratedRoundKind::Round0 => {
            let _ = writeln!(
                out,
                "      const auto *base_inputs = gkr_main_batch_payload_ptr<{}>(batch_static, batch_runtime.spill_payload, record.base_inputs, descriptors_inline);",
                round.base_descriptor_ty()
            );
            let _ = writeln!(
                out,
                "      const auto *extension_inputs = gkr_main_batch_payload_ptr<{}>(batch_static, batch_runtime.spill_payload, record.extension_inputs, descriptors_inline);",
                round.extension_descriptor_ty()
            );
            let _ = writeln!(
                out,
                "      const auto *base_outputs = gkr_main_batch_payload_ptr<gkr_base_initial_source<bf>>(batch_static, batch_runtime.spill_payload, record.base_outputs, descriptors_inline);"
            );
            let _ = writeln!(
                out,
                "      const auto *extension_outputs = gkr_main_batch_payload_ptr<gkr_ext_initial_source<E>>(batch_static, batch_runtime.spill_payload, record.extension_outputs, descriptors_inline);"
            );
            let _ = writeln!(
                out,
                "      const E *batch_challenges = batch_runtime.batch_challenges + {};",
                kernel.batch_challenge_offset
            );
            let _ = writeln!(
                out,
                "      const E auxiliary_challenge = {};",
                kernel.auxiliary_challenge_source.cpp_expr()
            );
            emit_constraint_block(out, layer_idx, kernel_idx, kernel.constraint.as_ref());
            let _ = writeln!(out, "      E c0;");
            let _ = writeln!(out, "      E c1;");
            let _ = writeln!(
                out,
                "      {}({}, base_inputs, extension_inputs, base_outputs, extension_outputs, batch_challenges, auxiliary_challenge, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);",
                round.value_call(),
                kernel.kind.cpp_name()
            );
        }
        GeneratedRoundKind::Round1Compact => {
            let _ = writeln!(
                out,
                "      const auto *base_inputs_src = gkr_main_batch_payload_ptr<{}>(batch_static, batch_runtime.spill_payload, record.base_inputs, descriptors_inline);",
                round.base_descriptor_ty()
            );
            let _ = writeln!(
                out,
                "      const auto *extension_inputs_src = gkr_main_batch_payload_ptr<{}>(batch_static, batch_runtime.spill_payload, record.extension_inputs, descriptors_inline);",
                round.extension_descriptor_ty()
            );
            emit_descriptor_copy_block(
                out,
                round.base_descriptor_ty(),
                "base_inputs_src",
                "base_inputs_storage",
                "base_inputs",
                &kernel.round1_base_first_access,
            );
            emit_descriptor_copy_block(
                out,
                round.extension_descriptor_ty(),
                "extension_inputs_src",
                "extension_inputs_storage",
                "extension_inputs",
                &kernel.round1_extension_first_access,
            );
            let _ = writeln!(
                out,
                "      const E *batch_challenges = batch_runtime.batch_challenges + {};",
                kernel.batch_challenge_offset
            );
            let _ = writeln!(
                out,
                "      const E auxiliary_challenge = {};",
                kernel.auxiliary_challenge_source.cpp_expr()
            );
            emit_constraint_block(out, layer_idx, kernel_idx, kernel.constraint.as_ref());
            let _ = writeln!(out, "      E c0;");
            let _ = writeln!(out, "      E c1;");
            let _ = writeln!(
                out,
                "      {}({}, base_inputs, extension_inputs, batch_challenges, batch_runtime.folding_challenge, auxiliary_challenge, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);",
                round.value_call(),
                kernel.kind.cpp_name()
            );
        }
        GeneratedRoundKind::Round2Compact => {
            let _ = writeln!(
                out,
                "      const auto *base_inputs_src = gkr_main_batch_payload_ptr<{}>(batch_static, batch_runtime.spill_payload, record.base_inputs, descriptors_inline);",
                round.base_descriptor_ty()
            );
            let _ = writeln!(
                out,
                "      const auto *extension_inputs_src = gkr_main_batch_payload_ptr<{}>(batch_static, batch_runtime.spill_payload, record.extension_inputs, descriptors_inline);",
                round.extension_descriptor_ty()
            );
            emit_descriptor_copy_block(
                out,
                round.base_descriptor_ty(),
                "base_inputs_src",
                "base_inputs_storage",
                "base_inputs",
                &kernel.round2_base_first_access,
            );
            emit_descriptor_copy_block(
                out,
                round.extension_descriptor_ty(),
                "extension_inputs_src",
                "extension_inputs_storage",
                "extension_inputs",
                &kernel.round2_extension_first_access,
            );
            let _ = writeln!(
                out,
                "      const E *batch_challenges = batch_runtime.batch_challenges + {};",
                kernel.batch_challenge_offset
            );
            let _ = writeln!(
                out,
                "      const E auxiliary_challenge = {};",
                kernel.auxiliary_challenge_source.cpp_expr()
            );
            emit_constraint_block(out, layer_idx, kernel_idx, kernel.constraint.as_ref());
            let _ = writeln!(out, "      E c0;");
            let _ = writeln!(out, "      E c1;");
            let _ = writeln!(
                out,
                "      {}({}, base_inputs, extension_inputs, batch_challenges, batch_runtime.folding_challenges, auxiliary_challenge, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);",
                round.value_call(),
                kernel.kind.cpp_name()
            );
        }
        GeneratedRoundKind::Round3Compact | GeneratedRoundKind::Round3Explicit => {
            let _ = writeln!(
                out,
                "      const auto *base_inputs_src = gkr_main_batch_payload_ptr<{}>(batch_static, batch_runtime.spill_payload, record.base_inputs, descriptors_inline);",
                round.base_descriptor_ty()
            );
            let _ = writeln!(
                out,
                "      const auto *extension_inputs_src = gkr_main_batch_payload_ptr<{}>(batch_static, batch_runtime.spill_payload, record.extension_inputs, descriptors_inline);",
                round.extension_descriptor_ty()
            );
            emit_descriptor_copy_block(
                out,
                round.base_descriptor_ty(),
                "base_inputs_src",
                "base_inputs_storage",
                "base_inputs",
                &kernel.round3_base_first_access,
            );
            emit_descriptor_copy_block(
                out,
                round.extension_descriptor_ty(),
                "extension_inputs_src",
                "extension_inputs_storage",
                "extension_inputs",
                &kernel.round3_extension_first_access,
            );
            let _ = writeln!(
                out,
                "      const E *batch_challenges = batch_runtime.batch_challenges + {};",
                kernel.batch_challenge_offset
            );
            let _ = writeln!(
                out,
                "      const E auxiliary_challenge = {};",
                kernel.auxiliary_challenge_source.cpp_expr()
            );
            emit_constraint_block(out, layer_idx, kernel_idx, kernel.constraint.as_ref());
            let _ = writeln!(out, "      E c0;");
            let _ = writeln!(out, "      E c1;");
            let _ = writeln!(
                out,
                "      {}({}, base_inputs, extension_inputs, batch_challenges, batch_runtime.folding_challenge, auxiliary_challenge, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);",
                round.value_call(),
                kernel.kind.cpp_name()
            );
        }
    }

    let _ = writeln!(out, "      total0 = E::add(total0, c0);");
    let _ = writeln!(out, "      total1 = E::add(total1, c1);");
    let _ = writeln!(out, "    }}");
}

fn emit_round_function(
    out: &mut String,
    spec: &GeneratedMainBackwardSpec,
    round: GeneratedRoundKind,
) {
    let _ = writeln!(
        out,
        "template <typename E>\nDEVICE_FORCEINLINE void {}(const u32 layer_idx, const {} &batch_static, const {} &batch_runtime, const gkr_generated_add_sub_lui_auipc_mop_main_challenges<E> &challenges, const unsigned acc_size) {{",
        round.function_name(),
        round.static_ty(),
        round.runtime_ty()
    );
    let _ = writeln!(
        out,
        "  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;"
    );
    let _ = writeln!(out, "  if (gid >= acc_size)");
    let _ = writeln!(out, "    return;");
    let _ = writeln!(out, "  E total0 = E::ZERO();");
    let _ = writeln!(out, "  E total1 = E::ZERO();");
    let _ = writeln!(out, "  switch (layer_idx) {{");
    for layer in spec.layers.iter() {
        let _ = writeln!(out, "  case {}:", layer.layer_idx);
        for (kernel_idx, kernel) in layer.kernels.iter().enumerate() {
            emit_kernel_block(out, layer.layer_idx, kernel_idx, kernel, round);
        }
        let _ = writeln!(out, "    break;");
    }
    let _ = writeln!(out, "  default:");
    let _ = writeln!(out, "    break;");
    let _ = writeln!(out, "  }}");
    let _ = writeln!(
        out,
        "  const E eq = load<E, ld_modifier::cs>(batch_runtime.eq_values, gid);"
    );
    let _ = writeln!(
        out,
        "  store<E, st_modifier::cs>(batch_runtime.contributions, E::mul(total0, eq), gid);"
    );
    let _ = writeln!(
        out,
        "  store<E, st_modifier::cs>(batch_runtime.contributions + acc_size, E::mul(total1, eq), gid);"
    );
    let _ = writeln!(out, "}}");
}

pub fn emit_add_sub_lui_auipc_mop_main_backward_header(spec: &GeneratedMainBackwardSpec) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "// Generated by gpu_witness_eval_generator::generate_add_sub_lui_auipc_mop_main_backward"
    );
    let _ = writeln!(out, "#pragma once\n");
    let _ = writeln!(out, "namespace airbender::prover::gkr {{");
    let _ = writeln!(out, "enum gkr_generated_main_challenge_source : u32 {{");
    let _ = writeln!(out, "  GKR_GENERATED_MAIN_SOURCE_ONE = 0,");
    for idx in 0..NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES {
        let _ = writeln!(
            out,
            "  GKR_GENERATED_MAIN_SOURCE_EXTERNAL_PERM_LINEARIZATION_{idx} = {},",
            idx + 1
        );
    }
    let _ = writeln!(
        out,
        "  GKR_GENERATED_MAIN_SOURCE_EXTERNAL_PERM_ADDITIVE = {},",
        NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES + 1
    );
    let _ = writeln!(
        out,
        "  GKR_GENERATED_MAIN_SOURCE_LOOKUP_MULTIPLICATIVE = {},",
        NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES + 2
    );
    let _ = writeln!(
        out,
        "  GKR_GENERATED_MAIN_SOURCE_LOOKUP_ADDITIVE = {},",
        NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES + 3
    );
    let _ = writeln!(
        out,
        "  GKR_GENERATED_MAIN_SOURCE_CONSTRAINT_BATCH = {},",
        NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES + 4
    );
    let _ = writeln!(out, "}};\n");

    let _ = writeln!(out, "struct gkr_generated_main_challenge_term {{");
    let _ = writeln!(out, "  u32 coeff;");
    let _ = writeln!(out, "  u32 source;");
    let _ = writeln!(out, "  u32 power;");
    let _ = writeln!(out, "  u32 reserved;");
    let _ = writeln!(out, "}};\n");

    let _ = writeln!(
        out,
        "template <typename E> struct gkr_generated_add_sub_lui_auipc_mop_main_challenges {{"
    );
    let _ = writeln!(
        out,
        "  E permutation_argument_linearization_challenges[{}];",
        NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES
    );
    let _ = writeln!(out, "  E permutation_argument_additive_part;");
    let _ = writeln!(out, "  E lookup_multiplicative_challenge;");
    let _ = writeln!(out, "  E lookup_additive_challenge;");
    let _ = writeln!(out, "  E constraint_batch_challenge;");
    let _ = writeln!(out, "}};\n");

    let _ = writeln!(
        out,
        "template <typename E>\nDEVICE_FORCEINLINE E gkr_generated_main_challenge_value(const gkr_generated_add_sub_lui_auipc_mop_main_challenges<E> &challenges, const u32 source) {{"
    );
    let _ = writeln!(out, "  switch (source) {{");
    let _ = writeln!(out, "  case GKR_GENERATED_MAIN_SOURCE_ONE:");
    let _ = writeln!(out, "    return E::ONE();");
    for idx in 0..NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES {
        let _ = writeln!(
            out,
            "  case GKR_GENERATED_MAIN_SOURCE_EXTERNAL_PERM_LINEARIZATION_{idx}:"
        );
        let _ = writeln!(
            out,
            "    return challenges.permutation_argument_linearization_challenges[{idx}];"
        );
    }
    let _ = writeln!(
        out,
        "  case GKR_GENERATED_MAIN_SOURCE_EXTERNAL_PERM_ADDITIVE:"
    );
    let _ = writeln!(
        out,
        "    return challenges.permutation_argument_additive_part;"
    );
    let _ = writeln!(
        out,
        "  case GKR_GENERATED_MAIN_SOURCE_LOOKUP_MULTIPLICATIVE:"
    );
    let _ = writeln!(
        out,
        "    return challenges.lookup_multiplicative_challenge;"
    );
    let _ = writeln!(out, "  case GKR_GENERATED_MAIN_SOURCE_LOOKUP_ADDITIVE:");
    let _ = writeln!(out, "    return challenges.lookup_additive_challenge;");
    let _ = writeln!(out, "  case GKR_GENERATED_MAIN_SOURCE_CONSTRAINT_BATCH:");
    let _ = writeln!(out, "    return challenges.constraint_batch_challenge;");
    let _ = writeln!(out, "  default:");
    let _ = writeln!(out, "    return E::ZERO();");
    let _ = writeln!(out, "  }}");
    let _ = writeln!(out, "}}\n");

    let _ = writeln!(
        out,
        "template <typename E>\nDEVICE_FORCEINLINE E gkr_generated_main_eval_terms(const gkr_generated_main_challenge_term *terms, const unsigned count, const gkr_generated_add_sub_lui_auipc_mop_main_challenges<E> &challenges) {{"
    );
    let _ = writeln!(out, "  E result = E::ZERO();");
    let _ = writeln!(out, "  for (unsigned i = 0; i < count; ++i) {{");
    let _ = writeln!(
        out,
        "    const E value = E::pow(gkr_generated_main_challenge_value<E>(challenges, terms[i].source), terms[i].power);"
    );
    let _ = writeln!(
        out,
        "    result = E::add(result, E::mul(value, bf::from_canonical_u32(terms[i].coeff)));"
    );
    let _ = writeln!(out, "  }}");
    let _ = writeln!(out, "  return result;");
    let _ = writeln!(out, "}}\n");

    emit_round_function(&mut out, spec, GeneratedRoundKind::Round0);
    out.push('\n');
    emit_round_function(&mut out, spec, GeneratedRoundKind::Round1Compact);
    out.push('\n');
    emit_round_function(&mut out, spec, GeneratedRoundKind::Round2Compact);
    out.push('\n');
    emit_round_function(&mut out, spec, GeneratedRoundKind::Round3Compact);
    out.push('\n');
    emit_round_function(&mut out, spec, GeneratedRoundKind::Round3Explicit);
    let _ = writeln!(out, "}} // namespace airbender::prover::gkr");
    out
}

pub fn generate_add_sub_lui_auipc_mop_main_backward_from_files(
    layout_path: impl AsRef<Path>,
) -> Result<String, Box<dyn std::error::Error>> {
    let layout = File::open(layout_path)?;
    let compiled_circuit: GKRCircuitArtifact<F> = serde_json::from_reader(layout)?;
    let spec = lower_add_sub_lui_auipc_mop_main_backward(&compiled_circuit)?;
    Ok(emit_add_sub_lui_auipc_mop_main_backward_header(&spec))
}

#[cfg(test)]
mod tests {
    use super::{
        emit_add_sub_lui_auipc_mop_main_backward_header,
        generate_add_sub_lui_auipc_mop_main_backward_from_files,
        lower_add_sub_lui_auipc_mop_main_backward,
    };
    use crate::F;
    use cs::gkr_compiler::GKRCircuitArtifact;
    use std::fs::File;
    use std::path::PathBuf;

    fn layout_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
            "../cs/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_layout_no_caches_gkr.json",
        )
    }

    fn golden_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
            "../gpu_prover/native/prover/gkr/generated/add_sub_lui_auipc_mop_main_backward_e4.cuh",
        )
    }

    fn load_layout() -> GKRCircuitArtifact<F> {
        let file = File::open(layout_path()).expect("layout JSON should exist");
        serde_json::from_reader(file).expect("layout JSON should deserialize")
    }

    #[test]
    fn add_sub_main_backward_header_is_deterministic() {
        let circuit = load_layout();
        let spec_a = lower_add_sub_lui_auipc_mop_main_backward(&circuit).unwrap();
        let spec_b = lower_add_sub_lui_auipc_mop_main_backward(&circuit).unwrap();
        let header_a = emit_add_sub_lui_auipc_mop_main_backward_header(&spec_a);
        let header_b = emit_add_sub_lui_auipc_mop_main_backward_header(&spec_b);
        assert_eq!(header_a, header_b);
    }

    #[test]
    fn add_sub_main_backward_header_matches_checked_in_golden() {
        let generated =
            generate_add_sub_lui_auipc_mop_main_backward_from_files(layout_path()).unwrap();
        let golden = std::fs::read_to_string(golden_path())
            .expect("checked-in generated header should exist");
        assert_eq!(generated, golden);
    }
}
