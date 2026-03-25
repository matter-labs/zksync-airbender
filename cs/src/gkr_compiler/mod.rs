// GKR compiler tries top optimally place variables into base/intermediate layers. There is no simple
// weight function to define optimization goal, but we can not avoid placing all memory related variables
// into the base layer.

use crate::definitions::gkr::GKRMemoryLayout;
use crate::definitions::gkr::GKRWitnessLayout;
use crate::definitions::gkr::NoFieldLinearRelation;
use crate::definitions::gkr::NoFieldSingleColumnLookupRelation;
use crate::definitions::gkr::NoFieldVectorLookupRelation;
use crate::definitions::gkr::RamWordRepresentation;
use crate::definitions::Degree1Constraint;
use crate::definitions::Degree2Constraint;
use crate::definitions::GKRAddress;
use crate::definitions::Variable;
use crate::definitions::REGISTER_SIZE;
use crate::gkr_compiler::graph::GraphHolder;
pub use crate::gkr_compiler::layout::GKRAuxLayoutData;
pub use crate::gkr_compiler::layout::GKRLayerDescription;
use common_constants::*;
use field::PrimeField;
use std::collections::*;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ShuffleRamTimestampComparisonPartialData {
    pub(crate) intermediate_borrow: Variable,
    pub(crate) read_timestamp: [Variable; 2],
    pub(crate) local_timestamp_in_cycle: usize,
}

mod compiled_constraint;
mod delegation_circuit;
pub(crate) mod delegation_mem_accesses;
mod family_circuit;
mod graph;
mod layout;
mod layout_utils;
mod lookup;
pub(crate) mod lookup_nodes;
pub(crate) mod memory_like_grand_product;
mod range_check_exprs;
mod utils;

pub use self::compiled_constraint::*;
pub(crate) use self::layout_utils::*;
pub(crate) use self::lookup::*;
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

#[serde_with::serde_as]
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
    pub num_generic_lookups: usize,
    pub placement_data: BTreeMap<Variable, GKRAddress>,
    pub generic_lookup_tables_width: usize,
    pub decode_table_columns_mask: Vec<bool>,
    pub tables_ids_in_generic_lookups: bool,

    // for satisfiability checks
    pub degree_2_constraints: Vec<Degree2Constraint<F>>,
    pub degree_1_constraints: Vec<Degree1Constraint<F>>,

    // for witness evaluation and multiplicity counting
    pub generic_lookups: Vec<NoFieldVectorLookupRelation>,
    pub range_check_16_lookup_expressions: Vec<NoFieldSingleColumnLookupRelation>,
    pub timestamp_range_check_lookup_expressions: Vec<NoFieldSingleColumnLookupRelation>,

    pub variable_names: BTreeMap<Variable, String>,
    #[serde_as(as = "Vec<(_, _)>")]
    pub scratch_space_mapping: BTreeMap<GKRAddress, usize>,
    pub scratch_space_mapping_rev: BTreeMap<usize, GKRAddress>,

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
    pub linear_terms: Box<[(u64, GKRAddress)]>,
    pub constant: u64,
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
    ConstantU16(u16),
    Constant(u32),
    U16Space(usize),
    U32Space([usize; 2]),
    U32SpaceSpecialIndirect {
        low_base: usize,
        low_dynamic_offset: Option<(u16, usize)>,
        low_offset: u32,
        high: usize,
    },
    U32SpaceGeneric([(Box<[(u64, usize)]>, u64); 2]),
}

impl CompiledAddressStrict {
    pub(crate) fn dependencies(&self) -> Vec<GKRAddress> {
        match self {
            Self::ConstantU16(..) => vec![],
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
                if let Some((_, low_dynamic_offset)) = low_dynamic_offset {
                    result.push(GKRAddress::BaseLayerMemory(*low_dynamic_offset));
                }

                result
            }
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CompiledMemoryTimestamp {
    Zero,
    Normal([usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM]),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldSpecialMemoryContributionRelation {
    pub address_space: CompiledAddressSpaceRelationStrict,
    pub address: CompiledAddressStrict,
    pub timestamp: CompiledMemoryTimestamp,
    pub value: RamWordRepresentation,
    pub timestamp_offset: u32,
}

impl NoFieldSpecialMemoryContributionRelation {
    pub(crate) fn dependencies(&self) -> Vec<GKRAddress> {
        let mut result = Vec::with_capacity(8);
        if let Some(a) = self.address_space.dependency() {
            result.push(a);
        }
        result.extend(self.address.dependencies());
        match self.timestamp {
            CompiledMemoryTimestamp::Zero => {}
            CompiledMemoryTimestamp::Normal(ts) => {
                result.extend(ts.map(|el| GKRAddress::BaseLayerMemory(el)));
            }
        }

        match self.value {
            RamWordRepresentation::Zero => {
                // nothing more
            }
            RamWordRepresentation::U16Limbs(els) => {
                result.extend(els.map(|el| GKRAddress::BaseLayerMemory(el)));
            }
            RamWordRepresentation::U8Limbs(els) => {
                result.extend(els.map(|el| GKRAddress::BaseLayerMemory(el)));
            }
        }

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
    LinearBaseFieldRelation {
        input: NoFieldLinearRelation,
        output: GKRAddress,
    },
    MaxQuadratic {
        input: NoFieldMaxQuadraticGKRRelation,
        output: GKRAddress,
    },

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

    // // a/b + 1/(c + gamma) where `c`` is in the base field and not cached
    // LookupUnbalancedPairWithBaseInputs {
    //     input: [GKRAddress; 2],
    //     remainder: NoFieldSingleColumnLookupRelation,
    //     output: [GKRAddress; 2],
    // },

    // // 1/(a+gamma) + multiplicity/(setup + gamma) where a is in base field and not cached
    // LookupFromBaseInputsWithSetup {
    //     input: NoFieldSingleColumnLookupRelation,
    //     setup: [GKRAddress; 2],
    //     output: [GKRAddress; 2],
    // },

    // 1/(a+gamma) + multiplicity/(setup + gamma) where a is in base field and materialized or cached
    LookupFromMaterializedBaseInputWithSetup {
        input: GKRAddress,
        setup: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // a/b + 1/(c + gamma) where `c`` is in the base field and is materialized or cached
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

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in in extension already due to vector nature (no caching)
    LookupPairFromMaterializedVectorInputs {
        input: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // 1/(a+gamma) + multiplicity/(setup + gamma) where a is in extension field and materialized or cached
    LookupFromMaterializedVectorInputWithSetup {
        input: GKRAddress,
        setup: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in in extension already due to vector nature (no caching)
    LookupPairFromCachedVectorInputs {
        input: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // a/b + 1/(c + gamma) where `c`` is in the extension field and is materialized or cached
    LookupUnbalancedPairWithMaterializedVectorInputs {
        input: [GKRAddress; 2],
        remainder: GKRAddress,
        output: [GKRAddress; 2],
    },

    // a/b + c/d -> (num, den)
    AggregateLookupRationalPair {
        input: [[GKRAddress; 2]; 2],
        output: [GKRAddress; 2],
    },
}

impl NoFieldGKRRelation {
    pub fn cached_addresses(&self) -> Vec<GKRAddress> {
        match self {
            // Self::FormalBaseLayerInput(..) => vec![],
            Self::LinearBaseFieldRelation { .. } => vec![],
            Self::MaxQuadratic { input, output } => vec![],
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
            // Self::LookupUnbalancedPairWithBaseInputs {
            //     input,
            //     remainder,
            //     output,
            // } => {
            //     vec![]
            // }
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                if remainder.is_cache() {
                    vec![*remainder]
                } else {
                    vec![]
                }
            }
            // Self::LookupFromBaseInputsWithSetup {
            //     input,
            //     setup,
            //     output,
            // } => {
            //     vec![]
            // }
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
            Self::LookupPairFromMaterializedVectorInputs { input, output } => {
                let mut result = vec![];
                for inp in input {
                    if inp.is_cache() {
                        result.push(inp);
                    }
                }

                input.to_vec()
            }
            Self::LookupPairFromCachedVectorInputs { input, output } => {
                assert!(input[0].is_cache());
                assert!(input[1].is_cache());

                input.to_vec()
            }
            Self::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                assert!(input[0].is_cache() == false);
                assert!(input[1].is_cache() == false);

                if remainder.is_cache() {
                    vec![*remainder]
                } else {
                    vec![]
                }
            }
            Self::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let mut caches = vec![];
                if input.is_cache() {
                    caches.push(*input);
                }
                assert!(setup[0].is_cache() == false);
                if setup[1].is_cache() {
                    caches.push(setup[1]);
                }
                caches
            }
            Self::AggregateLookupRationalPair { input, output } => {
                vec![]
            }
        }
    }

    pub fn created_claims(&self) -> Vec<GKRAddress> {
        match self {
            // Self::FormalBaseLayerInput(..) => vec![],
            Self::LinearBaseFieldRelation { input, output } => {
                let mut result = BTreeSet::new();
                for (_, el) in input.linear_terms.iter() {
                    result.insert(*el);
                }
                result.into_iter().collect()
            }
            Self::MaxQuadratic { input, output } => vec![],
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
            // Self::LookupUnbalancedPairWithBaseInputs {
            //     input,
            //     remainder,
            //     output,
            // } => {
            //     let mut result = BTreeSet::new();
            //     for (_, el) in remainder.input.linear_terms.iter() {
            //         result.insert(*el);
            //     }
            //     let mut result: Vec<GKRAddress> = result.into_iter().collect();
            //     result.extend_from_slice(input);
            //     result
            // }
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
            // Self::LookupFromBaseInputsWithSetup {
            //     input,
            //     setup,
            //     output,
            // } => {
            //     let mut result = BTreeSet::new();
            //     for (_, el) in input.input.linear_terms.iter() {
            //         result.insert(*el);
            //     }
            //     let mut result: Vec<GKRAddress> = result.into_iter().collect();
            //     result.extend_from_slice(setup);
            //     result
            // }
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
            Self::LookupPairFromMaterializedVectorInputs { input, output } => input.to_vec(),
            Self::LookupPairFromCachedVectorInputs { input, output } => input.to_vec(),
            Self::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                assert!(input.is_cache());
                assert!(setup[0].is_cache() == false);
                assert!(setup[1].is_cache());
                vec![setup[0]]
            }
            Self::AggregateLookupRationalPair { input, output } => {
                input.iter().flatten().copied().collect()
            }
            _ => {
                todo!();
            }
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NoFieldGKRCacheRelation {
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

pub fn compile_unrolled_circuit_state_transition_into_gkr<F: PrimeField>(
    table_addition_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>) -> (),
    circuit_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>) -> (),
    max_bytecode_size_in_words: usize,
    trace_len_log2: usize,
) -> GKRCircuitArtifact<F> {
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_trait::Circuit;
    use crate::gkr_compiler::GKRCompiler;

    let mut cs = BasicAssembly::<F>::new();
    (table_addition_fn)(&mut cs);
    (circuit_fn)(&mut cs);

    let (cs_output, _) = cs.finalize();

    let compiler = GKRCompiler::default();
    let compiled =
        compiler.compile_family_circuit(cs_output, max_bytecode_size_in_words, 0, trace_len_log2);

    compiled
}

pub fn compile_delegation_circuit_into_gkr<F: PrimeField>(
    table_addition_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>) -> (),
    circuit_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>) -> (),
    trace_len_log2: usize,
) -> GKRCircuitArtifact<F> {
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_trait::Circuit;
    use crate::gkr_compiler::GKRCompiler;

    let mut cs = BasicAssembly::<F>::new();
    (table_addition_fn)(&mut cs);
    (circuit_fn)(&mut cs);

    let (cs_output, _) = cs.finalize();

    let compiler = GKRCompiler::default();
    let compiled = compiler.compile_delegation_circuit(cs_output, trace_len_log2);

    compiled
}

use crate::witness_placer::graph_description::WitnessGraphCreator;

pub fn dump_wintess_graph<F: PrimeField>(
    table_addition_fn: &dyn Fn(
        &mut crate::cs::circuit_impl::BasicAssembly<F, WitnessGraphCreator<F>>,
    ) -> (),
    circuit_fn: &dyn Fn(
        &mut crate::cs::circuit_impl::BasicAssembly<F, WitnessGraphCreator<F>>,
    ) -> (),
) -> WitnessGraphCreator<F> {
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_trait::Circuit;

    let mut cs = BasicAssembly::<F, WitnessGraphCreator<F>>::new();
    cs.witness_placer = Some(WitnessGraphCreator::<F>::new());
    (table_addition_fn)(&mut cs);
    (circuit_fn)(&mut cs);

    let (artifact, mut witness_placer) = cs.finalize();
    if let Some(witness_placer) = witness_placer.as_mut() {
        witness_placer.variable_names = artifact.variable_names.clone();
    }

    witness_placer.unwrap()
}

pub fn dump_ssa_witness_eval_form<F: PrimeField>(
    table_addition_fn: &dyn Fn(
        &mut crate::cs::circuit_impl::BasicAssembly<F, WitnessGraphCreator<F>>,
    ) -> (),
    circuit_fn: &dyn Fn(
        &mut crate::cs::circuit_impl::BasicAssembly<F, WitnessGraphCreator<F>>,
    ) -> (),
) -> Vec<Vec<crate::witness_placer::graph_description::RawExpression<F>>> {
    let graph = dump_wintess_graph(table_addition_fn, circuit_fn);
    let (_resolution_order, ssa_forms) = graph.compute_resolution_order();
    ssa_forms
}
