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
use crate::structured_expr::StructuredStatement;
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
mod inits_and_teardowns;
mod inits_and_teardowns_inline;
mod layout;
mod lookup;
pub(crate) mod lookup_nodes;
pub(crate) mod memory_like_grand_product;
mod range_check_exprs;
mod utils;

pub use self::compiled_constraint::*;
pub use self::inits_and_teardowns::*;
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

pub use crate::definitions::OutputType;

#[derive(Default)]
pub struct GKRCompiler<F: PrimeField> {
    _marker: std::marker::PhantomData<F>,
}

#[serde_with::serde_as]
#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct GKRCircuitArtifact<F: PrimeField> {
    pub trace_len: usize,
    pub table_offsets: Vec<u32>,
    pub total_tables_size: usize,
    pub offset_for_decoder_table: usize,
    pub has_decoder_lookup: bool,
    pub layers: Vec<GKRLayerDescription<F>>,
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
    pub structured_statements: Vec<StructuredStatement<F>>,

    // for witness evaluation and multiplicity counting
    pub generic_lookups: Vec<NoFieldVectorLookupRelation<F>>,
    pub range_check_16_lookup_expressions: Vec<NoFieldSingleColumnLookupRelation<F>>,
    pub timestamp_range_check_lookup_expressions: Vec<NoFieldSingleColumnLookupRelation<F>>,

    pub variable_names: BTreeMap<Variable, String>,
    #[serde_as(as = "Vec<(_, _)>")]
    pub scratch_space_mapping: BTreeMap<GKRAddress, usize>,
    pub scratch_space_mapping_rev: BTreeMap<usize, GKRAddress>,

    pub aux_layout_data: GKRAuxLayoutData,
    _marker: core::marker::PhantomData<F>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldMaxQuadraticGKRRelation<F: PrimeField> {
    #[expect(clippy::type_complexity)]
    pub quadratic_terms: Box<[(GKRAddress, Box<[(F, GKRAddress)]>)]>,
    pub linear_terms: Box<[(F, GKRAddress)]>,
    pub constant: F,
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
    #[expect(clippy::type_complexity)]
    U32SpaceGeneric([(Box<[(u64, GKRAddress)]>, u64); 2]),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CompiledAddressSpaceRelationStrict {
    Constant(u32),
    IsRegister(usize), // must contribute 0 (register) if "true", 1 (RAM) otherwise
    IsRam(usize),      // must contribute 0 (register) if "false", 1 (RAM) otherwise
}

impl CompiledAddressSpaceRelationStrict {
    pub(crate) fn dependency(&self) -> Option<GKRAddress> {
        match self {
            Self::Constant(..) => None,
            Self::IsRegister(offset) | Self::IsRam(offset) => {
                Some(GKRAddress::BaseLayerMemory(*offset))
            }
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
    #[expect(clippy::type_complexity)]
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
                low_offset: _,
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
                result.extend(ts.map(GKRAddress::BaseLayerMemory));
            }
        }

        match self.value {
            RamWordRepresentation::Zero => {
                // nothing more
            }
            RamWordRepresentation::U16Limbs(els) => {
                result.extend(els.map(GKRAddress::BaseLayerMemory));
            }
            RamWordRepresentation::U8Limbs(els) => {
                result.extend(els.map(GKRAddress::BaseLayerMemory));
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
pub struct NoFieldMaxQuadraticConstraintsGKRRelation<F: PrimeField> {
    #[expect(clippy::type_complexity)]
    pub quadratic_terms: Box<[((GKRAddress, GKRAddress), Box<[(F, usize)]>)]>,
    #[expect(clippy::type_complexity)]
    pub linear_terms: Box<[(GKRAddress, Box<[(F, usize)]>)]>,
    pub constants: Box<[(F, usize)]>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum InitsOrTeardownsTimestampAndValue {
    Init, // zeroes
    Teardown {
        lhs_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        lhs_value: [usize; 2],
        rhs_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        rhs_value: [usize; 2],
    },
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NoFieldStructuredExpression<F: PrimeField> {
    Constant(F),
    Place(GKRAddress),
    Sum(Vec<Self>),
    Product(Vec<Self>),
}

impl<F: PrimeField> PartialOrd for NoFieldStructuredExpression<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl<F: PrimeField> Ord for NoFieldStructuredExpression<F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Constant(a), Self::Constant(b)) => {
                // can happen in recursive comparisons below
                a.as_u128_reduced().cmp(&b.as_u128_reduced())
            }
            (Self::Constant(..), _) => std::cmp::Ordering::Less,
            (_, Self::Constant(..)) => std::cmp::Ordering::Greater,
            (Self::Place(a), Self::Place(b)) => a.cmp(b),
            (Self::Place(..), _) => std::cmp::Ordering::Less,
            (_, Self::Place(..)) => std::cmp::Ordering::Greater,
            (Self::Product(a), Self::Product(b)) => {
                if a.len() < b.len() {
                    std::cmp::Ordering::Less
                } else if a.len() > b.len() {
                    std::cmp::Ordering::Greater
                } else {
                    // recursive
                    a.cmp(b)
                }
            }
            (Self::Product(..), _) => std::cmp::Ordering::Less,
            (_, Self::Product(..)) => std::cmp::Ordering::Greater,
            (Self::Sum(a), Self::Sum(b)) => {
                if a.len() < b.len() {
                    std::cmp::Ordering::Less
                } else if a.len() > b.len() {
                    std::cmp::Ordering::Greater
                } else {
                    // recursive
                    a.cmp(b)
                }
            }
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NoFieldGKRRelation<F: PrimeField> {
    LinearBaseFieldRelation {
        input: NoFieldLinearRelation<F>,
        output: GKRAddress,
    },
    MaxQuadratic {
        input: NoFieldMaxQuadraticGKRRelation<F>,
        expression: NoFieldStructuredExpression<F>,
        output: GKRAddress,
    },

    EnforceSingleMaxQuadraticConstraint {
        input: NoFieldMaxQuadraticGKRRelation<F>,
        expression: NoFieldStructuredExpression<F>,
    },

    // Enforces a randomized set of constraints in a form of c1 + alpha * c2 + ...
    // Sorted as: each quadratic term is recorded once (they are in base field), and powers of alpha are recorded
    EnforceConstraintsMaxQuadratic {
        input: NoFieldMaxQuadraticConstraintsGKRRelation<F>,
    },
    // SpecialConstraintCollapse(NoFieldSpecialConstraintCollapseGKRRelation),
    // LookupTrivialDenominator(NoFieldLookupTrivialDenominatorRelation),
    // LookupAggregationPostTrivialNumerator(NoFieldLookupPostTrivialNumeratorRelation),

    // Copy across GKR layers, relation is a(x) = \sum_y eq(x, y) a(y) formally
    CopyInBaseField {
        input: GKRAddress,
        output: GKRAddress,
    },
    CopyInExtensionField {
        input: GKRAddress,
        output: GKRAddress,
    },
    // Memory-like argument related

    // Computes (memory tuple) * (memory tuple)
    InitialGrandProductFromCaches {
        input: [GKRAddress; 2],
        output: GKRAddress,
    },
    // Computes (memory tuple) * (memory tuple) without intermediate cache relations
    InitialGrandProductWithoutCaches {
        input: [NoFieldSpecialMemoryContributionRelation; 2],
        output: GKRAddress,
    },
    // Computes (memory tuple) * (single scalar in extension)
    UnbalancedGrandProductWithCache {
        scalar: GKRAddress,
        input: GKRAddress,
        output: GKRAddress,
    },
    // Materialize memory expression
    MaterializeGrandProductTermExpression {
        input: NoFieldSpecialMemoryContributionRelation,
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
        input: NoFieldSingleColumnLookupRelation<F>,
        output: GKRAddress,
        range_check_width: u32,
    },
    // Computes linear relation for vector lookup and places it into variable in extension field
    MaterializedVectorLookupInput {
        input: NoFieldVectorLookupRelation<F>,
        output: GKRAddress,
    },

    // Expects denominators to be cached, and computes a/b - c/d -> (num, den)
    LookupWithCachedDensAndSetup {
        input: [GKRAddress; 2],
        setup: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },
    // Expects denominators to be cached, and computes a/b - c/d -> (num, den)
    LookupWithDensAndSetupExpressions {
        input: (GKRAddress, NoFieldVectorLookupRelation<F>),
        setup: (GKRAddress, Box<[GKRAddress]>),
        output: [GKRAddress; 2],
    },

    // LookupLinearNumeratorFromCaches([GKRAddress; 2]),
    // LookupDenominatorFromCaches([GKRAddress; 2]),

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in base field
    LookupPairFromBaseInputs {
        input: [NoFieldSingleColumnLookupRelation<F>; 2],
        output: [GKRAddress; 2],
        range_check_width: u32,
    },

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in base field and materialized
    LookupPairFromMaterializedBaseInputs {
        input: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // // a/b + 1/(c + gamma) where `c`` is in the base field and not cached
    // LookupUnbalancedPairWithBaseInputs {
    //     input: [GKRAddress; 2],
    //     remainder: NoFieldSingleColumnLookupRelation<F>,
    //     output: [GKRAddress; 2],
    // },

    // // 1/(a+gamma) + multiplicity/(setup + gamma) where a is in base field and not cached
    // LookupFromBaseInputsWithSetup {
    //     input: NoFieldSingleColumnLookupRelation<F>,
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

    // LookupNumeratorFromBaseInputs([NoFieldLinearRelation<F>; 2]),
    // LookupDenominatorFromBaseInputs([NoFieldLinearRelation<F>; 2]),

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in in extension already due to vector nature (no caching)
    LookupPairFromVectorInputs {
        input: [NoFieldVectorLookupRelation<F>; 2],
        output: [GKRAddress; 2],
    },

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in in extension already due to vector nature (no caching)
    LookupPairFromMaterializedVectorInputs {
        input: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },

    // 1/(a+gamma) + multiplicity/(setup + gamma) where a is in extension field
    LookupFromVectorInputWithSetup {
        input: NoFieldVectorLookupRelation<F>,
        setup: (GKRAddress, Box<[GKRAddress]>),
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

    // a/b + 1/(c + gamma) where `c`` is in the extension field
    LookupUnbalancedPairWithVectorInputs {
        input: [GKRAddress; 2],
        remainder: NoFieldVectorLookupRelation<F>,
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

    InitsOrTeardownsInitialPair {
        timestamp_and_value: InitsOrTeardownsTimestampAndValue,
        setup: [GKRAddress; 2], // virtual
        output: GKRAddress,
        set_idxes: [usize; 2], // defines upper bits of address
    },
}

impl<F: PrimeField> NoFieldGKRRelation<F> {
    pub fn cached_addresses(&self) -> Vec<GKRAddress> {
        match self {
            // Self::FormalBaseLayerInput(..) => vec![],
            Self::LinearBaseFieldRelation { .. } => vec![],
            Self::MaxQuadratic { .. } => vec![],
            Self::EnforceConstraintsMaxQuadratic { input: _ } => vec![],
            Self::CopyInBaseField { input, output } => {
                assert!(!output.is_cache());

                if input.is_cache() {
                    vec![*input]
                } else {
                    vec![]
                }
            }
            Self::CopyInExtensionField { input, output } => {
                assert!(!output.is_cache());

                if input.is_cache() {
                    vec![*input]
                } else {
                    vec![]
                }
            }
            Self::InitialGrandProductFromCaches { input, output } => {
                assert!(input[0].is_cache());
                assert!(input[1].is_cache());
                assert!(!output.is_cache());

                input.to_vec()
            }
            Self::InitialGrandProductWithoutCaches {
                input: _,
                output: _,
            } => {
                vec![]
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {
                assert!(input.is_cache());
                assert!(!scalar.is_cache());
                assert!(!output.is_cache());

                vec![*scalar]
            }
            Self::TrivialProduct { input, output } => {
                assert!(!input[0].is_cache());
                assert!(!input[1].is_cache());
                assert!(!output.is_cache());

                vec![]
            }
            Self::MaskIntoIdentityProduct {
                input: _,
                mask: _,
                output: _,
            } => {
                vec![]
            }
            Self::MaterializeSingleLookupInput { .. } => {
                vec![]
            }
            Self::MaterializedVectorLookupInput {
                input: _,
                output: _,
            } => {
                vec![]
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output: _,
            } => {
                assert!(!input[0].is_cache());
                assert!(input[1].is_cache());
                assert!(!setup[0].is_cache());
                assert!(setup[1].is_cache());

                vec![input[1], setup[1]]
            }
            Self::LookupWithDensAndSetupExpressions { .. } => {
                vec![]
            }
            Self::LookupPairFromBaseInputs { .. } => {
                vec![]
            }
            Self::LookupPairFromMaterializedBaseInputs { input, output: _ } => {
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
                input: _,
                remainder,
                output: _,
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
                setup: _,
                output: _,
            } => {
                if input.is_cache() {
                    vec![*input]
                } else {
                    vec![]
                }
            }
            Self::LookupPairFromVectorInputs {
                input: _,
                output: _,
            } => {
                vec![]
            }
            Self::LookupPairFromMaterializedVectorInputs { input, output: _ } => {
                let mut result = vec![];
                for inp in input {
                    if inp.is_cache() {
                        result.push(*inp);
                    }
                }

                result
            }
            Self::LookupPairFromCachedVectorInputs { input, output: _ } => {
                assert!(input[0].is_cache());
                assert!(input[1].is_cache());

                input.to_vec()
            }
            Self::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output: _,
            } => {
                assert!(!input[0].is_cache());
                assert!(!input[1].is_cache());

                if remainder.is_cache() {
                    vec![*remainder]
                } else {
                    vec![]
                }
            }
            Self::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output: _,
            } => {
                let mut caches = vec![];
                if input.is_cache() {
                    caches.push(*input);
                }
                assert!(!setup[0].is_cache());
                if setup[1].is_cache() {
                    caches.push(setup[1]);
                }
                caches
            }
            Self::AggregateLookupRationalPair {
                input: _,
                output: _,
            } => {
                vec![]
            }
            Self::LookupUnbalancedPairWithVectorInputs { .. } => {
                vec![]
            }
            Self::LookupFromVectorInputWithSetup { .. } => {
                vec![]
            }
            Self::MaterializeGrandProductTermExpression { .. } => {
                vec![]
            }
            Self::EnforceSingleMaxQuadraticConstraint { .. } => {
                vec![]
            }
            Self::InitsOrTeardownsInitialPair { .. } => {
                vec![]
            }
        }
    }

    /// Dump inputs for data flow. Sumcheck will make new claims evaluations of these
    /// inputs at random point
    pub fn dump_inputs(&self, result: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::LinearBaseFieldRelation { input, output: _ } => {
                for (_, el) in input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::MaxQuadratic { input, .. } => {
                for (a, other) in input.quadratic_terms.iter() {
                    result.insert(*a);
                    for (_, b) in other.iter() {
                        result.insert(*b);
                    }
                }
                for (_, a) in input.linear_terms.iter() {
                    result.insert(*a);
                }
            }
            Self::EnforceConstraintsMaxQuadratic { input } => {
                for ((a, b), _) in input.quadratic_terms.iter() {
                    result.insert(*a);
                    result.insert(*b);
                }
                for (el, _) in input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::CopyInBaseField { input, .. } | Self::CopyInExtensionField { input, .. } => {
                result.insert(*input);
            }
            Self::InitialGrandProductFromCaches { input, output: _ } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::InitialGrandProductWithoutCaches { input, output: _ } => {
                input[0].dump_inputs(result);
                input[1].dump_inputs(result);
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output: _,
            } => {
                result.insert(*scalar);
                result.insert(*input);
            }
            Self::TrivialProduct { input, output: _ } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output: _,
            } => {
                result.insert(*input);
                result.insert(*mask);
            }
            Self::MaterializeSingleLookupInput { input, .. } => {
                for (_, el) in input.input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::MaterializedVectorLookupInput { input, output: _ } => {
                for el in input.columns.iter() {
                    for (_, el) in el.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output: _,
            } => {
                result.insert(input[0]);
                result.insert(input[1]);
                result.insert(setup[0]);
                result.insert(setup[1]);
            }
            Self::LookupPairFromBaseInputs { input, .. } => {
                for el in input.iter() {
                    for (_, el) in el.input.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
            }
            Self::LookupPairFromMaterializedBaseInputs { input, output: _ } => {
                result.insert(input[0]);
                result.insert(input[1]);
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
                output: _,
            } => {
                result.insert(input[0]);
                result.insert(input[1]);
                result.insert(*remainder);
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
                output: _,
            } => {
                result.insert(*input);
                result.insert(setup[0]);
                result.insert(setup[1]);
            }
            Self::LookupPairFromVectorInputs { input, output: _ } => {
                for input in input.iter() {
                    for el in input.columns.iter() {
                        for (_, el) in el.linear_terms.iter() {
                            result.insert(*el);
                        }
                    }
                }
            }
            Self::LookupPairFromMaterializedVectorInputs { input, output: _ } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::LookupPairFromCachedVectorInputs { input, output: _ } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => {
                result.insert(*input);
                result.insert(setup[0]);
                result.insert(setup[1]);
            }
            Self::AggregateLookupRationalPair { input, output: _ } => {
                result.insert(input[0][0]);
                result.insert(input[0][1]);
                result.insert(input[1][0]);
                result.insert(input[1][1]);
            }
            a => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }

    /// Dump outputs for data flow. Sumcheck will use claims about evaluations of these
    /// polys at random point as the starting point
    pub fn dump_outputs(&self, result: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::LinearBaseFieldRelation { input: _, output } => {
                result.insert(*output);
            }
            Self::MaxQuadratic {
                input: _, output, ..
            } => {
                result.insert(*output);
            }
            Self::EnforceConstraintsMaxQuadratic { input: _ } => {
                // nothing
            }
            Self::CopyInBaseField { output, .. } | Self::CopyInExtensionField { output, .. } => {
                result.insert(*output);
            }
            Self::InitialGrandProductFromCaches { input: _, output } => {
                result.insert(*output);
            }
            Self::InitialGrandProductWithoutCaches { input: _, output } => {
                result.insert(*output);
            }
            Self::UnbalancedGrandProductWithCache {
                scalar: _,
                input: _,
                output,
            } => {
                result.insert(*output);
            }
            Self::TrivialProduct { input: _, output } => {
                result.insert(*output);
            }
            Self::MaskIntoIdentityProduct {
                input: _,
                mask: _,
                output,
            } => {
                result.insert(*output);
            }
            Self::MaterializeSingleLookupInput {
                input: _, output, ..
            } => {
                result.insert(*output);
            }
            Self::MaterializedVectorLookupInput { input: _, output } => {
                result.insert(*output);
            }
            Self::LookupWithCachedDensAndSetup {
                input: _,
                setup: _,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromBaseInputs {
                input: _, output, ..
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromMaterializedBaseInputs { input: _, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
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
                input: _,
                remainder: _,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
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
                input: _,
                setup: _,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromVectorInputs { input: _, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromMaterializedVectorInputs { input: _, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromCachedVectorInputs { input: _, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupFromMaterializedVectorInputWithSetup {
                input: _,
                setup: _,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::AggregateLookupRationalPair { input: _, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            a => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NoFieldGKRCacheRelation<F: PrimeField> {
    SingleColumnLookup {
        relation: NoFieldSingleColumnLookupRelation<F>,
        range_check_width: usize,
    },
    VectorizedLookup(NoFieldVectorLookupRelation<F>),
    MemoryTuple(NoFieldSpecialMemoryContributionRelation),
    VectorizedLookupSetup(Box<[GKRAddress]>),
}

impl<F: PrimeField> NoFieldGKRCacheRelation<F> {
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
pub struct GateArtifacts<F: PrimeField> {
    pub output_layer: usize,
    pub enforced_relation: NoFieldGKRRelation<F>,
}

pub trait GKRGate<F: PrimeField> {
    type Output: 'static + Sized;

    fn short_name(&self) -> String;

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder<F>,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation<F>);
}

pub fn compile_unrolled_circuit_state_transition_into_gkr<F: PrimeField>(
    table_addition_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>),
    circuit_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>),
    max_bytecode_size_in_words: usize,
    trace_len_log2: usize,
    num_init_and_teardown_pairs: usize,
) -> GKRCircuitArtifact<F> {
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_trait::Circuit;
    use crate::gkr_compiler::GKRCompiler;

    let mut cs = BasicAssembly::<F>::new();
    (table_addition_fn)(&mut cs);
    (circuit_fn)(&mut cs);

    let (cs_output, _) = cs.finalize();

    let compiler = GKRCompiler::default();
    compiler.compile_family_circuit(
        cs_output,
        max_bytecode_size_in_words,
        num_init_and_teardown_pairs,
        trace_len_log2,
        true,
    )
}

pub fn compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches<F: PrimeField>(
    table_addition_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>),
    circuit_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>),
    max_bytecode_size_in_words: usize,
    trace_len_log2: usize,
    num_init_and_teardown_pairs: usize,
) -> GKRCircuitArtifact<F> {
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_trait::Circuit;
    use crate::gkr_compiler::GKRCompiler;

    let mut cs = BasicAssembly::<F>::new();
    (table_addition_fn)(&mut cs);
    (circuit_fn)(&mut cs);

    let (cs_output, _) = cs.finalize();

    let compiler = GKRCompiler::default();
    compiler.compile_family_circuit(
        cs_output,
        max_bytecode_size_in_words,
        num_init_and_teardown_pairs,
        trace_len_log2,
        false,
    )
}

pub fn compile_delegation_circuit_into_gkr<F: PrimeField>(
    table_addition_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>),
    circuit_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>),
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
    compiler.compile_delegation_circuit(cs_output, trace_len_log2, true)
}

pub fn compile_delegation_circuit_into_gkr_without_caches<F: PrimeField>(
    table_addition_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>),
    circuit_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F>),
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
    compiler.compile_delegation_circuit(cs_output, trace_len_log2, false)
}

use crate::witness_placer::graph_description::WitnessGraphCreator;

#[expect(clippy::type_complexity)]
pub fn dump_wintess_graph<F: PrimeField>(
    table_addition_fn: &dyn Fn(
        &mut crate::cs::circuit_impl::BasicAssembly<F, WitnessGraphCreator<F>>,
    ),
    circuit_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F, WitnessGraphCreator<F>>),
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

#[expect(clippy::type_complexity)]
pub fn dump_ssa_witness_eval_form<F: PrimeField>(
    table_addition_fn: &dyn Fn(
        &mut crate::cs::circuit_impl::BasicAssembly<F, WitnessGraphCreator<F>>,
    ),
    circuit_fn: &dyn Fn(&mut crate::cs::circuit_impl::BasicAssembly<F, WitnessGraphCreator<F>>),
) -> Vec<Vec<crate::witness_placer::graph_description::RawExpression<F>>> {
    let graph = dump_wintess_graph(table_addition_fn, circuit_fn);
    let (_resolution_order, ssa_forms) = graph.compute_resolution_order();
    ssa_forms
}
