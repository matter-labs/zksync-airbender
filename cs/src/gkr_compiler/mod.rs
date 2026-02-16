// GKR compiler tries top optimally place variables into base/intermediate layers. There is no simple
// weight function to define optimization goal, but we can not avoid placing all memory related variables
// into the base layer.

use crate::cs::circuit::CircuitOutput;
use crate::definitions::gkr::GKRMemoryLayout;
use crate::definitions::gkr::GKRWitnessLayout;
use crate::definitions::Degree1Constraint;
use crate::definitions::Degree2Constraint;
use crate::definitions::GKRAddress;
use crate::definitions::Variable;
use crate::definitions::REGISTER_SIZE;
use crate::gkr_compiler::graph::GraphHolder;
pub use crate::gkr_compiler::layout::GKRAuxLayoutData;
pub use crate::gkr_compiler::layout::GKRLayerDescription;
use crate::one_row_compiler::gkr::NoFieldLinearRelation;
use crate::one_row_compiler::gkr::NoFieldSingleColumnLookupRelation;
use crate::one_row_compiler::gkr::NoFieldVectorLookupRelation;
use common_constants::*;
use field::PrimeField;
use std::collections::*;

mod compiled_constraint;
mod family_circuit;
mod graph;
// mod graphviz;
mod layout;
mod lookup;
pub(crate) mod lookup_nodes;
pub(crate) mod memory_like_grand_product;
mod range_check_exprs;
mod utils;

pub use self::compiled_constraint::*;
pub use self::lookup::*;
pub(crate) use self::utils::*;

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum LookupType {
    RangeCheck16,
    TimestampRangeCheck,
    Generic,
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum OutputType {
    PermutationProduct = 0,
    Lookup16Bits,
    LookupTimestamps,
    GenericLookup,
}

#[derive(Default)]
pub struct GKRCompiler<F: PrimeField> {
    _marker: std::marker::PhantomData<F>,
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct GKRCircuitArtifact<F: PrimeField> {
    pub trace_len: usize,
    pub table_offsets: Vec<u32>,
    pub total_tables_size: usize,
    pub offset_for_decoder_table: usize,
    pub has_decoder_lookup: bool,
    pub layers: Vec<GKRLayerDescription>,
    pub global_output_map: BTreeMap<OutputType, Vec<GKRAddress>>,

    pub memory_layout: GKRMemoryLayout,
    pub witness_layout: GKRWitnessLayout,
    pub scratch_space_size: usize,
    pub placement_data: BTreeMap<Variable, GKRAddress>,
    pub generic_lookup_tables_width: usize,
    pub decode_table_columns_mask: Vec<bool>,
    pub tables_ids_in_generic_lookups: bool,

    pub degree_2_constraints: Vec<Degree2Constraint<F>>,
    pub degree_1_constraints: Vec<Degree1Constraint<F>>,

    pub variable_names: BTreeMap<Variable, String>,

    pub aux_layout_data: GKRAuxLayoutData,
    _marker: core::marker::PhantomData<F>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct PureQuadraticGKRRelation<F: PrimeField> {
    pub terms: Box<[(GKRAddress, Box<(F, GKRAddress)>)]>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MaxQuadraticGKRRelation<F: PrimeField> {
    pub quadratic_terms: Box<[(GKRAddress, Box<(F, GKRAddress)>)]>,
    pub linear_terms: Box<(F, GKRAddress)>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SpecialConstraintCollapseGKRRelation<F: PrimeField> {
    pub predicate: GKRAddress,
    pub remainder_from_quadratic: GKRAddress,
    pub sparse_linear_remainders: Box<[Option<GKRAddress>]>,
    pub sparse_constant_remainders: Box<[F]>,
    pub num_terms: usize,
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub enum GKRRelation<F: PrimeField> {
    PureQuadratic(PureQuadraticGKRRelation<F>),
    MaxQuadratic(MaxQuadraticGKRRelation<F>),
    SpecialConstraintCollapse(SpecialConstraintCollapseGKRRelation<F>),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldPureQuadraticGKRRelation {
    pub terms: Box<[(GKRAddress, Box<[(u64, GKRAddress)]>)]>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldMaxQuadraticGKRRelation {
    pub quadratic_terms: Box<[(GKRAddress, Box<[(u64, GKRAddress)]>)]>,
    pub linear_terms: Box<[Box<[(u64, GKRAddress)]>]>,
    pub constants: Box<[u64]>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldSpecialConstraintCollapseGKRRelation {
    pub predicate: GKRAddress,
    pub remainder_from_quadratic: GKRAddress,
    pub sparse_linear_remainders: Box<[Box<[(u64, GKRAddress)]>]>,
    pub sparse_constant_remainders: Box<[u64]>,
    pub num_terms: usize,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CompiledAddressSpaceRelation {
    Constant(u32),
    Pos(GKRAddress),
    Neg(GKRAddress),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CompiledAddress {
    Constant(u32),
    U16Space(GKRAddress),
    U32Space([GKRAddress; 2]),
    U32SpaceSpecialIndirect {
        low_base: GKRAddress,
        low_dynamic_offset: Option<GKRAddress>,
        low_offset: u64,
        high: GKRAddress,
    },
    U32SpaceGeneric([(Box<[(u64, GKRAddress)]>, u64); 2]),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CompiledAddressSpaceRelationStrict {
    Constant(u32),
    Is(usize),
    Not(usize),
}

impl CompiledAddressSpaceRelationStrict {
    pub(crate) fn dependency(&self) -> Option<GKRAddress> {
        match self {
            Self::Constant(..) => None,
            Self::Is(offset) | Self::Not(offset) => Some(GKRAddress::BaseLayerMemory(*offset)),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CompiledAddressStrict {
    Constant(u32),
    U16Space(usize),
    U32Space([usize; 2]),
    U32SpaceSpecialIndirect {
        low_base: usize,
        low_dynamic_offset: Option<usize>,
        low_offset: u64,
        high: usize,
    },
    U32SpaceGeneric([(Box<[(u64, usize)]>, u64); 2]),
}

impl CompiledAddressStrict {
    pub(crate) fn dependencies(&self) -> Vec<GKRAddress> {
        match self {
            Self::Constant(..) => vec![],
            Self::U16Space(offset) => vec![GKRAddress::BaseLayerMemory(*offset)],
            Self::U32Space(offsets) => vec![
                GKRAddress::BaseLayerMemory(offsets[0]),
                GKRAddress::BaseLayerMemory(offsets[1]),
            ],
            Self::U32SpaceGeneric(..) => todo!(),
            Self::U32SpaceSpecialIndirect {
                low_base,
                low_dynamic_offset,
                low_offset,
                high,
            } => {
                let mut result = Vec::with_capacity(3);
                result.push(GKRAddress::BaseLayerMemory(*low_base));
                result.push(GKRAddress::BaseLayerMemory(*high));
                if let Some(low_dynamic_offset) = low_dynamic_offset {
                    result.push(GKRAddress::BaseLayerMemory(*low_dynamic_offset));
                }

                result
            }
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldSpecialMemoryContributionRelation {
    pub address_space: CompiledAddressSpaceRelationStrict,
    pub address: CompiledAddressStrict,
    pub timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub value: [usize; REGISTER_SIZE],
    pub timestamp_offset: u32,
}

impl NoFieldSpecialMemoryContributionRelation {
    pub(crate) fn dependencies(&self) -> Vec<GKRAddress> {
        let mut result = Vec::with_capacity(8);
        if let Some(a) = self.address_space.dependency() {
            result.push(a);
        }
        result.extend(self.address.dependencies());
        result.extend(self.timestamp.map(|el| GKRAddress::BaseLayerMemory(el)));
        result.extend(self.value.map(|el| GKRAddress::BaseLayerMemory(el)));

        result
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldLookupTrivialDenominatorRelation {
    pub parts: [GKRAddress; 2],
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldLookupPostTrivialNumeratorRelation {
    pub parts: [(NoFieldLookupTrivialDenominatorRelation, GKRAddress); 2],
}

// quadratic terms: term -> (constant, power of random challenge)
// linear terms: term -> (constant, power of random challenge)
// constant temrs: (constant, power of random challenge)
#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldMaxQuadraticConstraintsGKRRelation {
    pub quadratic_terms: Box<[((GKRAddress, GKRAddress), Box<[(u32, usize)]>)]>,
    pub linear_terms: Box<[(GKRAddress, Box<[(u32, usize)]>)]>,
    pub constants: Box<[(u32, usize)]>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NoFieldGKRRelation {
    // FormalBaseLayerInput(GKRAddress),
    // PureQuadratic {
    //     input: NoFieldPureQuadraticGKRRelation,
    //     output: GKRAddress,
    // },
    // MaxQuadratic {
    //     input: NoFieldMaxQuadraticGKRRelation,
    //     output: GKRAddress,
    // },

    // Enforces a randomized set of constraints in a form of c1 + alpha * c2 + ...
    // Sorted as: each quadratic term is recorded once (they are in base field), and powers of alpha are recorded
    EnforceConstraintsMaxQuadratic {
        input: NoFieldMaxQuadraticConstraintsGKRRelation,
    },
    // SpecialConstraintCollapse(NoFieldSpecialConstraintCollapseGKRRelation),
    // LookupTrivialDenominator(NoFieldLookupTrivialDenominatorRelation),
    // LookupAggregationPostTrivialNumerator(NoFieldLookupPostTrivialNumeratorRelation),

    // Copy across GKR layers, relation is a(x) = \sum_y eq(x, y) a(y) formally
    Copy {
        input: GKRAddress,
        output: GKRAddress,
    },

    // Memory-like argument related

    // Computes (memory tuple) * (memory tuple)
    InitialGrandProductFromCaches {
        input: [GKRAddress; 2],
        output: GKRAddress,
    },
    // Computes (memory tuple) * (single scalar in extension)
    UnbalancedGrandProductWithCache {
        scalar: GKRAddress,
        input: GKRAddress,
        output: GKRAddress,
    },
    // Computes (single scalar in extension) * (single scalar in extension)
    TrivialProduct {
        input: [GKRAddress; 2],
        output: GKRAddress,
    },
    // Computes input * mask + 1 * (1 - mask)
    MaskIntoIdentityProduct {
        input: GKRAddress,
        mask: GKRAddress,
        output: GKRAddress,
    },

    // Lookup argument related
    // Computes linear relation and places it into variable in base field
    MaterializeSingleLookupInput {
        input: NoFieldSingleColumnLookupRelation,
        output: GKRAddress,
    },
    // Computes linear relation for vector lookup and places it into variable in extension field
    MaterializedVectorLookupInput {
        input: NoFieldVectorLookupRelation,
        output: GKRAddress,
    },
    // // Expects both inputs to come from caches, and o
    // LookupPairFromCaches {
    //     input: [[GKRAddress; 2]; 2],
    //     output: [GKRAddress; 2],
    // },
    // Expects denominators to be cached, and computes a/b - c/d -> (num, den)
    LookupWithCachedDensAndSetup {
        input: [GKRAddress; 2],
        setup: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // LookupLinearNumeratorFromCaches([GKRAddress; 2]),
    // LookupDenominatorFromCaches([GKRAddress; 2]),

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in base field
    LookupPairFromBaseInputs {
        input: [NoFieldSingleColumnLookupRelation; 2],
        output: [GKRAddress; 2],
    },

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in base field and materialized
    LookupPairFromMaterializedBaseInputs {
        input: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // a/b + 1/(c + gamma) where `c`` is in the base field
    LookupUnbalancedPairWithBaseInputs {
        input: [GKRAddress; 2],
        remainder: NoFieldSingleColumnLookupRelation,
        output: [GKRAddress; 2],
    },
    // 1/(a+gamma) + multiplicity/(setup + gamma) where a is in base field
    LookupFromBaseInputsWithSetup {
        input: NoFieldSingleColumnLookupRelation,
        setup: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // 1/(a+gamma) + multiplicity/(setup + gamma) where a is in base field and materialized
    LookupFromMaterializedBaseInputWithSetup {
        input: GKRAddress,
        setup: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // a/b + 1/(c + gamma) where `c`` is in the base field and is materialized
    LookupUnbalancedPairWithMaterializedBaseInputs {
        input: [GKRAddress; 2],
        remainder: GKRAddress,
        output: [GKRAddress; 2],
    },

    // LookupNumeratorFromBaseInputs([NoFieldLinearRelation; 2]),
    // LookupDenominatorFromBaseInputs([NoFieldLinearRelation; 2]),

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in in extension already due to vector nature (no caching)
    LookupPairFromVectorInputs {
        input: [NoFieldVectorLookupRelation; 2],
        output: [GKRAddress; 2],
    },

    // LookupNumeratorFromVectorInputs([NoFieldVectorLookupRelation; 2]),
    // LookupDenominatorFromVectorInputs([NoFieldVectorLookupRelation; 2]),

    // a/b + c/d -> (num, den)
    LookupPair {
        input: [[GKRAddress; 2]; 2],
        output: [GKRAddress; 2],
    },
    // LookupNumeratorContinueAggregation([GKRAddress; 2]),
    // LookupDenominatorContinueAggregation([GKRAddress; 2]),
}

impl NoFieldGKRRelation {
    pub fn cached_addresses(&self) -> Vec<GKRAddress> {
        match self {
            // Self::FormalBaseLayerInput(..) => vec![],
            Self::EnforceConstraintsMaxQuadratic { input } => vec![],
            Self::Copy { input, output } => {
                assert!(output.is_cache() == false);

                if input.is_cache() {
                    vec![*input]
                } else {
                    vec![]
                }
            }
            Self::InitialGrandProductFromCaches { input, output } => {
                assert!(input[0].is_cache());
                assert!(input[1].is_cache());
                assert!(output.is_cache() == false);

                input.to_vec()
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {
                assert!(input.is_cache());
                assert!(scalar.is_cache() == false);
                assert!(output.is_cache() == false);

                vec![*scalar]
            }
            Self::TrivialProduct { input, output } => {
                assert!(input[0].is_cache() == false);
                assert!(input[1].is_cache() == false);
                assert!(output.is_cache() == false);

                vec![]
            }
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                vec![]
            }
            Self::MaterializeSingleLookupInput { input, output } => {
                vec![]
            }
            Self::MaterializedVectorLookupInput { input, output } => {
                vec![]
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                assert!(input[0].is_cache() == false);
                assert!(input[1].is_cache());
                assert!(setup[0].is_cache() == false);
                assert!(setup[1].is_cache());

                vec![input[1], setup[1]]
            }
            Self::LookupPairFromBaseInputs { input, output } => {
                vec![]
            }
            Self::LookupPairFromMaterializedBaseInputs { input, output } => {
                let mut all_cached = vec![];
                for el in input.iter() {
                    if el.is_cache() {
                        all_cached.push(*el);
                    }
                }

                all_cached
            }
            Self::LookupUnbalancedPairWithBaseInputs {
                input,
                remainder,
                output,
            } => {
                vec![]
            }
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                vec![]
            }
            Self::LookupFromBaseInputsWithSetup {
                input,
                setup,
                output,
            } => {
                vec![]
            }
            Self::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                if input.is_cache() {
                    vec![*input]
                } else {
                    vec![]
                }
            }
            Self::LookupPairFromVectorInputs { input, output } => {
                vec![]
            }
            Self::LookupPair { input, output } => {
                vec![]
            }
        }
    }

    pub fn expected_input_claims(&self) -> Vec<GKRAddress> {
        // they are also the outputs

        todo!()
    }

    pub fn created_claims(&self) -> Vec<GKRAddress> {
        match self {
            // Self::FormalBaseLayerInput(..) => vec![],
            Self::EnforceConstraintsMaxQuadratic { input } => {
                let mut result = BTreeSet::new();
                for ((a, b), _) in input.quadratic_terms.iter() {
                    result.insert(*a);
                    result.insert(*b);
                }
                for (el, _) in input.linear_terms.iter() {
                    result.insert(*el);
                }
                result.into_iter().collect()
            }
            Self::Copy { input, output } => {
                vec![*input]
            }
            Self::InitialGrandProductFromCaches { input, output } => {
                vec![]
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {
                vec![*scalar]
            }
            Self::TrivialProduct { input, output } => input.to_vec(),
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                vec![*input, *mask]
            }
            Self::MaterializeSingleLookupInput { input, output } => {
                let mut result = BTreeSet::new();
                for (_, el) in input.input.linear_terms.iter() {
                    result.insert(*el);
                }
                result.into_iter().collect()
            }
            Self::MaterializedVectorLookupInput { input, output } => {
                let mut result = BTreeSet::new();
                for el in input.columns.iter() {
                    for (_, el) in el.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
                result.into_iter().collect()
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                vec![]
            }
            Self::LookupPairFromBaseInputs { input, output } => {
                let mut result = BTreeSet::new();
                for el in input.iter() {
                    for (_, el) in el.input.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
                result.into_iter().collect()
            }
            Self::LookupPairFromMaterializedBaseInputs { input, output } => {
                vec![]
            }
            Self::LookupUnbalancedPairWithBaseInputs {
                input,
                remainder,
                output,
            } => {
                let mut result = BTreeSet::new();
                for (_, el) in remainder.input.linear_terms.iter() {
                    result.insert(*el);
                }
                let mut result: Vec<GKRAddress> = result.into_iter().collect();
                result.extend_from_slice(input);
                result
            }
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let mut result: Vec<GKRAddress> = vec![];
                result.extend_from_slice(input);
                result.push(*remainder);
                result
            }
            Self::LookupFromBaseInputsWithSetup {
                input,
                setup,
                output,
            } => {
                let mut result = BTreeSet::new();
                for (_, el) in input.input.linear_terms.iter() {
                    result.insert(*el);
                }
                let mut result: Vec<GKRAddress> = result.into_iter().collect();
                result.extend_from_slice(setup);
                result
            }
            Self::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                vec![]
            }
            Self::LookupPairFromVectorInputs { input, output } => {
                let mut result = BTreeSet::new();
                for input in input.iter() {
                    for el in input.columns.iter() {
                        for (_, el) in el.linear_terms.iter() {
                            result.insert(*el);
                        }
                    }
                }
                result.into_iter().collect()
            }
            Self::LookupPair { input, output } => input.iter().flatten().copied().collect(),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NoFieldGKRCacheRelation {
    LongLinear,
    SingleColumnLookup {
        relation: NoFieldSingleColumnLookupRelation,
        range_check_width: usize,
    },
    VectorizedLookup(NoFieldVectorLookupRelation),
    MemoryTuple(NoFieldSpecialMemoryContributionRelation),
    VectorizedLookupSetup(Box<[GKRAddress]>),
}

impl NoFieldGKRCacheRelation {
    pub fn dependencies(&self) -> Vec<GKRAddress> {
        match self {
            Self::LongLinear => {
                vec![]
            }
            Self::SingleColumnLookup { relation, .. } => {
                let mut result = vec![];
                for (_, pos) in relation.input.linear_terms.iter() {
                    result.push(*pos);
                }

                result
            }
            Self::VectorizedLookup(vl) => {
                let mut result = vec![];
                for el in vl.columns.iter() {
                    for (_, pos) in el.linear_terms.iter() {
                        result.push(*pos);
                    }
                }

                result
            }
            Self::VectorizedLookupSetup(s) => s.to_vec(),
            Self::MemoryTuple(mt) => mt.dependencies(),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct GateArtifacts {
    pub output_layer: usize,
    pub enforced_relation: NoFieldGKRRelation,
}

pub trait GKRGate {
    type Output: 'static + Sized;

    fn short_name(&self) -> String;

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation);
}
