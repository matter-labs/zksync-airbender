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

pub mod codegen_ir;
pub use codegen_ir::{lower, to_json_string, CodegenCircuit};
pub mod dag_ir;
mod compiled_constraint;
mod delegation_circuit;
pub(crate) mod delegation_mem_accesses;
mod family_circuit;
mod graph;
mod inits_and_teardowns;
mod layout;
mod lookup;
pub(crate) mod lookup_nodes;
pub(crate) mod memory_like_grand_product;
mod range_check_exprs;
#[cfg(any(test, feature = "test-support"))]
pub mod test_support;
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
    pub structured_statements: Vec<StructuredStatement<F>>,

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
    pub quadratic_terms: Box<[(GKRAddress, Box<[(u32, GKRAddress)]>)]>,
    pub linear_terms: Box<[(u32, GKRAddress)]>,
    pub constant: u32,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NoFieldStructuredExpression {
    Constant(u32),
    Place(GKRAddress),
    Sum(Vec<NoFieldStructuredExpression>),
    Product(Vec<NoFieldStructuredExpression>),
}

impl PartialOrd for NoFieldStructuredExpression {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl Ord for NoFieldStructuredExpression {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Constant(..), Self::Constant(..)) => {
                unreachable!("unnormalized")
            }
            (Self::Constant(..), _) => std::cmp::Ordering::Less,
            (_, Self::Constant(..)) => std::cmp::Ordering::Greater,
            (Self::Place(a), Self::Place(b)) => a.cmp(b),
            (Self::Place(..), _) => std::cmp::Ordering::Less,
            (_, Self::Place(..)) => std::cmp::Ordering::Greater,
            (Self::Product(..), _) => std::cmp::Ordering::Less,
            (_, Self::Product(..)) => std::cmp::Ordering::Greater,
            (Self::Sum(..), _) => std::cmp::Ordering::Greater,
            (_, Self::Sum(..)) => std::cmp::Ordering::Less,
        }
    }
}

impl NoFieldStructuredExpression {
    pub fn degree(&self) -> usize {
        match self {
            Self::Constant(_) => 0,
            Self::Place(_) => 1,
            Self::Sum(terms) => terms.iter().map(Self::degree).max().unwrap_or(0),
            Self::Product(factors) => factors.iter().map(Self::degree).sum(),
        }
    }

    pub fn assert_well_formed(&self) {
        match self {
            Self::Constant(_) => {}
            Self::Place(_) => {}
            Self::Sum(terms) => {
                assert!(self.degree() > 0, "constants must be collapsed");
            }
            Self::Product(factors) => {
                let mut constant_found = false;
                for el in factors.iter() {
                    if let Self::Constant(..) = el {
                        if constant_found == false {
                            constant_found = true;
                        } else {
                            panic!("constants must be collapsed");
                        }
                    }
                }
            }
        }
    }
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
pub enum NoFieldGKRRelation {
    LinearBaseFieldRelation {
        input: NoFieldLinearRelation,
        output: GKRAddress,
    },
    MaxQuadratic {
        input: NoFieldMaxQuadraticGKRRelation,
        expression: NoFieldStructuredExpression,
        output: GKRAddress,
    },

    EnforceSingleMaxQuadraticConstraint {
        input: NoFieldMaxQuadraticGKRRelation,
        expression: NoFieldStructuredExpression,
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
        input: NoFieldSingleColumnLookupRelation,
        output: GKRAddress,
        range_check_width: u32,
    },
    // Computes linear relation for vector lookup and places it into variable in extension field
    MaterializedVectorLookupInput {
        input: NoFieldVectorLookupRelation,
        output: GKRAddress,
    },

    // Expects denominators to be cached, and computes a/b - c/d -> (num, den)
    LookupWithCachedDensAndSetup {
        input: [GKRAddress; 2],
        setup: [GKRAddress; 2],
        output: [GKRAddress; 2],
    },
    // Expects denominators to be not cached, and computes a/b - c/d -> (num, den)
    LookupWithDensAndSetupExpressions {
        input: (GKRAddress, NoFieldVectorLookupRelation),
        setup: (GKRAddress, Box<[GKRAddress]>),
        output: [GKRAddress; 2],
    },
    // Expects input denominators to be not cached, but setup - cached, and computes a/b - c/d -> (num, den)
    LookupWithDensAndCachedSetup {
        input: (GKRAddress, NoFieldVectorLookupRelation),
        setup: (GKRAddress, GKRAddress),
        output: [GKRAddress; 2],
    },

    // LookupLinearNumeratorFromCaches([GKRAddress; 2]),
    // LookupDenominatorFromCaches([GKRAddress; 2]),

    // 1/(a+gamma) + 1/(b + gamma) where a, b are in base field
    LookupPairFromBaseInputs {
        input: [NoFieldSingleColumnLookupRelation; 2],
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

    // 1/(a+gamma) + multiplicity/(setup + gamma) where a is in extension field
    LookupFromVectorInputWithSetup {
        input: NoFieldVectorLookupRelation,
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
        remainder: NoFieldVectorLookupRelation,
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

impl NoFieldGKRRelation {
    pub fn cached_addresses(&self) -> Vec<GKRAddress> {
        match self {
            // Self::FormalBaseLayerInput(..) => vec![],
            Self::LinearBaseFieldRelation { .. } => vec![],
            Self::MaxQuadratic { input, output, .. } => vec![],
            Self::EnforceConstraintsMaxQuadratic { input } => vec![],
            Self::CopyInBaseField { input, output } => {
                assert!(output.is_cache() == false);

                if input.is_cache() {
                    vec![*input]
                } else {
                    vec![]
                }
            }
            Self::CopyInExtensionField { input, output } => {
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
            Self::InitialGrandProductWithoutCaches { input, output } => {
                vec![]
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
            Self::MaterializeSingleLookupInput { input, output, .. } => {
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
            Self::LookupWithDensAndSetupExpressions { .. } => {
                vec![]
            }
            Self::LookupPairFromBaseInputs { input, output, .. } => {
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
            Self::LookupWithDensAndCachedSetup { setup, .. } => {
                vec![setup.1]
            }
            a @ _ => {
                panic!("{:?} is not yet supported", a);
            }
        }
    }

    /// Dump inputs for data flow. Sumcheck will make new claims evaluations of these
    /// inputs at random point
    pub fn dump_inputs(&self, result: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::LinearBaseFieldRelation { input, output } => {
                for (_, el) in input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::MaxQuadratic { input, output, .. } => {
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
            Self::InitialGrandProductFromCaches { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::InitialGrandProductWithoutCaches { input, output } => {
                input[0].dump_inputs(result);
                input[1].dump_inputs(result);
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {
                result.insert(*scalar);
                result.insert(*input);
            }
            Self::TrivialProduct { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                result.insert(*input);
                result.insert(*mask);
            }
            Self::MaterializeSingleLookupInput { input, output, .. } => {
                for (_, el) in input.input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::MaterializedVectorLookupInput { input, output } => {
                for el in input.columns.iter() {
                    for (_, el) in el.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                result.insert(input[0]);
                result.insert(input[1]);
                result.insert(setup[0]);
                result.insert(setup[1]);
            }
            Self::LookupPairFromBaseInputs { input, output, .. } => {
                for el in input.iter() {
                    for (_, el) in el.input.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
            }
            Self::LookupPairFromMaterializedBaseInputs { input, output } => {
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
                output,
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
                output,
            } => {
                result.insert(*input);
                result.insert(setup[0]);
                result.insert(setup[1]);
            }
            Self::LookupPairFromVectorInputs { input, output } => {
                for input in input.iter() {
                    for el in input.columns.iter() {
                        for (_, el) in el.linear_terms.iter() {
                            result.insert(*el);
                        }
                    }
                }
            }
            Self::LookupPairFromMaterializedVectorInputs { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::LookupPairFromCachedVectorInputs { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => {
                result.insert(*input);
                result.insert(setup[0]);
                result.insert(setup[1]);
            }
            Self::AggregateLookupRationalPair { input, output } => {
                result.insert(input[0][0]);
                result.insert(input[0][1]);
                result.insert(input[1][0]);
                result.insert(input[1][1]);
            }
            Self::LookupWithDensAndSetupExpressions { input, setup, .. } => {
                result.insert(input.0);
                for el in input.1.columns.iter() {
                    for (_, el) in el.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
                result.insert(setup.0);
                for el in setup.1.iter() {
                    result.insert(*el);
                }
            }
            Self::EnforceSingleMaxQuadraticConstraint { input, .. } => {
                for (a, other) in input.quadratic_terms.iter() {
                    result.insert(*a);
                    for (_, b) in other.iter() {
                        result.insert(*b);
                    }
                }
                for (_, el) in input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::LookupWithDensAndCachedSetup { input, setup, .. } => {
                result.insert(input.0);
                for el in input.1.columns.iter() {
                    for (_, el) in el.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
                result.insert(setup.0);
                result.insert(setup.1);
            }
            a @ _ => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }

    /// Dump outputs for data flow. Sumcheck will use claims about evaluations of these
    /// polys at random point as the starting point
    pub fn dump_outputs(&self, result: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::LinearBaseFieldRelation { input, output } => {
                result.insert(*output);
            }
            Self::MaxQuadratic { input, output, .. } => {
                result.insert(*output);
            }
            Self::EnforceConstraintsMaxQuadratic { input } => {
                // nothing
            }
            Self::CopyInBaseField { output, .. } | Self::CopyInExtensionField { output, .. } => {
                result.insert(*output);
            }
            Self::InitialGrandProductFromCaches { input, output } => {
                result.insert(*output);
            }
            Self::InitialGrandProductWithoutCaches { input, output } => {
                result.insert(*output);
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {
                result.insert(*output);
            }
            Self::TrivialProduct { input, output } => {
                result.insert(*output);
            }
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                result.insert(*output);
            }
            Self::MaterializeSingleLookupInput { input, output, .. } => {
                result.insert(*output);
            }
            Self::MaterializedVectorLookupInput { input, output } => {
                result.insert(*output);
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromBaseInputs { input, output, .. } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromMaterializedBaseInputs { input, output } => {
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
                input,
                remainder,
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
                input,
                setup,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromVectorInputs { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromMaterializedVectorInputs { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromCachedVectorInputs { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::AggregateLookupRationalPair { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupWithDensAndCachedSetup { output, .. } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            a @ _ => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }

    /// Dump inputs for data flow. Sumcheck will make new claims evaluations of these
    /// inputs at random point
    pub fn dump_base_field_inputs(&self, result: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::LinearBaseFieldRelation { input, output } => {
                for (_, el) in input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::MaxQuadratic { input, output, .. } => {
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
            Self::CopyInBaseField { input, .. } => {
                result.insert(*input);
            }
            Self::InitialGrandProductFromCaches { input, output } => {}
            Self::InitialGrandProductWithoutCaches { input, output } => {
                input[0].dump_inputs(result);
                input[1].dump_inputs(result);
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {}
            Self::TrivialProduct { input, output } => {}
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                result.insert(*mask);
            }
            Self::MaterializeSingleLookupInput { input, output, .. } => {
                for (_, el) in input.input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::MaterializedVectorLookupInput { input, output } => {
                for el in input.columns.iter() {
                    for (_, el) in el.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {}
            Self::LookupPairFromBaseInputs { input, output, .. } => {
                for el in input.iter() {
                    for (_, el) in el.input.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
            }
            Self::LookupPairFromMaterializedBaseInputs { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                result.insert(*remainder);
            }
            Self::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                result.insert(*input);
                result.insert(setup[0]);
                result.insert(setup[1]);
            }
            Self::LookupPairFromVectorInputs { input, output } => {
                for input in input.iter() {
                    for el in input.columns.iter() {
                        for (_, el) in el.linear_terms.iter() {
                            result.insert(*el);
                        }
                    }
                }
            }
            Self::LookupPairFromMaterializedVectorInputs { input, output } => {}
            Self::LookupPairFromCachedVectorInputs { input, output } => {}
            Self::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => {}
            Self::AggregateLookupRationalPair { input, output } => {}
            Self::LookupWithDensAndSetupExpressions { input, setup, .. } => {
                result.insert(input.0);
                for el in input.1.columns.iter() {
                    for (_, el) in el.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
                result.insert(setup.0);
                for el in setup.1.iter() {
                    result.insert(*el);
                }
            }
            Self::EnforceSingleMaxQuadraticConstraint { input, .. } => {
                for (a, other) in input.quadratic_terms.iter() {
                    result.insert(*a);
                    for (_, b) in other.iter() {
                        result.insert(*b);
                    }
                }
                for (_, el) in input.linear_terms.iter() {
                    result.insert(*el);
                }
            }
            Self::LookupWithDensAndCachedSetup { input, setup, .. } => {
                result.insert(input.0);
                for el in input.1.columns.iter() {
                    for (_, el) in el.linear_terms.iter() {
                        result.insert(*el);
                    }
                }
                result.insert(setup.0);
            }
            a @ _ => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }

    pub fn dump_ext_field_inputs(&self, result: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::LinearBaseFieldRelation { input, output } => {}
            Self::MaxQuadratic { input, output, .. } => {}
            Self::EnforceSingleMaxQuadraticConstraint { input, .. } => {}
            Self::EnforceConstraintsMaxQuadratic { input } => {}
            Self::CopyInBaseField { input, .. } => {}
            Self::CopyInExtensionField { input, .. } => {
                result.insert(*input);
            }
            Self::InitialGrandProductFromCaches { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::InitialGrandProductWithoutCaches { input, output } => {}
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {
                result.insert(*scalar);
                result.insert(*input);
            }
            Self::TrivialProduct { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                result.insert(*input);
            }
            Self::MaterializeSingleLookupInput { input, output, .. } => {}
            Self::MaterializedVectorLookupInput { input, output } => {}
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                result.insert(input[0]);
                result.insert(input[1]);
                result.insert(setup[0]);
                result.insert(setup[1]);
            }
            Self::LookupPairFromBaseInputs { input, output, .. } => {}
            Self::LookupPairFromMaterializedBaseInputs { input, output } => {}
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {}
            Self::LookupPairFromVectorInputs { input, output } => {}
            Self::LookupPairFromMaterializedVectorInputs { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::LookupPairFromCachedVectorInputs { input, output } => {
                result.insert(input[0]);
                result.insert(input[1]);
            }
            Self::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => {
                result.insert(*input);
                result.insert(setup[1]);
            }
            Self::AggregateLookupRationalPair { input, output } => {}
            Self::LookupWithDensAndSetupExpressions { input, setup, .. } => {}
            Self::LookupWithDensAndCachedSetup { input, setup, .. } => {
                result.insert(setup.1);
            }
            a @ _ => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }

    /// Dump outputs for data flow. Sumcheck will use claims about evaluations of these
    /// polys at random point as the starting point
    pub fn dump_base_field_outputs(&self, result: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::LinearBaseFieldRelation { input, output } => {
                result.insert(*output);
            }
            Self::MaxQuadratic { input, output, .. } => {
                result.insert(*output);
            }
            Self::EnforceSingleMaxQuadraticConstraint { input, .. } => {}
            Self::EnforceConstraintsMaxQuadratic { input } => {
                // nothing
            }
            Self::CopyInBaseField { output, .. } => {
                result.insert(*output);
            }
            Self::CopyInExtensionField { output, .. } => {}
            Self::InitialGrandProductFromCaches { input, output } => {}
            Self::InitialGrandProductWithoutCaches { input, output } => {}
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {}
            Self::TrivialProduct { input, output } => {}
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {}
            Self::MaterializeSingleLookupInput { input, output, .. } => {
                result.insert(*output);
            }
            Self::MaterializedVectorLookupInput { input, output } => {}
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {}
            Self::LookupPairFromBaseInputs { input, output, .. } => {}
            Self::LookupPairFromMaterializedBaseInputs { input, output } => {}
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {}
            Self::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {}
            Self::LookupPairFromVectorInputs { input, output } => {}
            Self::LookupPairFromMaterializedVectorInputs { input, output } => {}
            Self::LookupPairFromCachedVectorInputs { input, output } => {}
            Self::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {}
            Self::AggregateLookupRationalPair { input, output } => {}
            Self::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {}
            Self::LookupWithDensAndCachedSetup { output, .. } => {}
            a @ _ => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }

    /// Dump outputs for data flow. Sumcheck will use claims about evaluations of these
    /// polys at random point as the starting point
    pub fn dump_ext_field_outputs(&self, result: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::LinearBaseFieldRelation { input, output } => {}
            Self::MaxQuadratic { input, output, .. } => {}
            Self::EnforceSingleMaxQuadraticConstraint { input, .. } => {}
            Self::EnforceConstraintsMaxQuadratic { input } => {
                // nothing
            }
            Self::CopyInBaseField { output, .. } => {}
            Self::CopyInExtensionField { output, .. } => {
                result.insert(*output);
            }
            Self::InitialGrandProductFromCaches { input, output } => {
                result.insert(*output);
            }
            Self::InitialGrandProductWithoutCaches { input, output } => {
                result.insert(*output);
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {
                result.insert(*output);
            }
            Self::TrivialProduct { input, output } => {
                result.insert(*output);
            }
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                result.insert(*output);
            }
            Self::MaterializeSingleLookupInput { input, output, .. } => {}
            Self::MaterializedVectorLookupInput { input, output } => {
                result.insert(*output);
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromBaseInputs { input, output, .. } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromMaterializedBaseInputs { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromVectorInputs { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromMaterializedVectorInputs { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupPairFromCachedVectorInputs { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::AggregateLookupRationalPair { input, output } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            Self::LookupWithDensAndCachedSetup { output, .. } => {
                result.insert(output[0]);
                result.insert(output[1]);
            }
            a @ _ => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }

    pub fn ordered_outputs_for_batching(&self) -> Vec<GKRAddress> {
        match self {
            Self::LinearBaseFieldRelation { input, output } => {
                vec![*output]
            }
            Self::MaxQuadratic { input, output, .. } => {
                vec![*output]
            }
            Self::EnforceSingleMaxQuadraticConstraint { input, .. } => {
                vec![]
            }
            Self::EnforceConstraintsMaxQuadratic { input } => {
                vec![]
            }
            Self::CopyInBaseField { output, .. } => {
                vec![*output]
            }
            Self::CopyInExtensionField { output, .. } => {
                vec![*output]
            }
            Self::InitialGrandProductFromCaches { input, output } => {
                vec![*output]
            }
            Self::InitialGrandProductWithoutCaches { input, output } => {
                vec![*output]
            }
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => {
                vec![*output]
            }
            Self::TrivialProduct { input, output } => {
                vec![*output]
            }
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                vec![*output]
            }
            Self::MaterializeSingleLookupInput { input, output, .. } => {
                vec![*output]
            }
            Self::MaterializedVectorLookupInput { input, output } => {
                vec![*output]
            }
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => output.to_vec(),

            Self::LookupPairFromBaseInputs { input, output, .. } => output.to_vec(),
            Self::LookupPairFromMaterializedBaseInputs { input, output } => output.to_vec(),
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => output.to_vec(),
            Self::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => output.to_vec(),
            Self::LookupPairFromVectorInputs { input, output } => output.to_vec(),
            Self::LookupPairFromMaterializedVectorInputs { input, output } => output.to_vec(),
            Self::LookupPairFromCachedVectorInputs { input, output } => output.to_vec(),
            Self::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => output.to_vec(),
            Self::AggregateLookupRationalPair { input, output } => output.to_vec(),
            Self::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => output.to_vec(),
            Self::LookupWithDensAndCachedSetup { output, .. } => output.to_vec(),
            a @ _ => {
                panic!("Not yet implemented for relation {:?}", a);
            }
        }
    }

    /// Dump inputs for data flow. Sumcheck will make new claims evaluations of these
    /// inputs at random point
    pub fn num_challenges(&self) -> usize {
        match self {
            Self::LinearBaseFieldRelation { input, output } => 1,
            Self::MaxQuadratic { input, output, .. } => 1,
            Self::EnforceConstraintsMaxQuadratic { input } => 1,
            Self::CopyInBaseField { input, .. } | Self::CopyInExtensionField { input, .. } => 1,
            Self::InitialGrandProductFromCaches { input, output } => 1,
            Self::InitialGrandProductWithoutCaches { input, output } => 1,
            Self::UnbalancedGrandProductWithCache {
                scalar,
                input,
                output,
            } => 1,
            Self::TrivialProduct { input, output } => 1,
            Self::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => 1,
            Self::MaterializeSingleLookupInput { input, output, .. } => 1,
            Self::MaterializedVectorLookupInput { input, output } => 1,
            Self::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => 2,
            Self::LookupPairFromBaseInputs { input, output, .. } => 2,
            Self::LookupPairFromMaterializedBaseInputs { input, output } => 2,
            Self::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => 2,
            Self::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => 2,
            Self::LookupPairFromVectorInputs { input, output } => 2,
            Self::LookupPairFromMaterializedVectorInputs { input, output } => 2,
            Self::LookupPairFromCachedVectorInputs { input, output } => 2,
            Self::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => 2,
            Self::AggregateLookupRationalPair { input, output } => 2,
            Self::LookupWithDensAndSetupExpressions { input, setup, .. } => 2,
            Self::EnforceSingleMaxQuadraticConstraint { input, .. } => 1,
            Self::LookupWithDensAndCachedSetup { .. } => 2,
            a @ _ => {
                panic!("Not yet implemented for relation {:?}", a);
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

    pub fn dump_base_field_inputs(&self, dst: &mut BTreeSet<GKRAddress>) {
        match self {
            Self::SingleColumnLookup { relation, .. } => {
                for (_, pos) in relation.input.linear_terms.iter() {
                    dst.insert(*pos);
                }
            }
            Self::VectorizedLookup(vl) => {
                for el in vl.columns.iter() {
                    for (_, pos) in el.linear_terms.iter() {
                        dst.insert(*pos);
                    }
                }
            }
            Self::VectorizedLookupSetup(s) => {
                for pos in s.iter() {
                    dst.insert(*pos);
                }
            }
            Self::MemoryTuple(mt) => {
                for pos in mt.dependencies().into_iter() {
                    dst.insert(pos);
                }
            }
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
    let compiled = compiler.compile_family_circuit(
        cs_output,
        max_bytecode_size_in_words,
        0,
        trace_len_log2,
        true,
    );

    compiled
}

pub fn compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches<F: PrimeField>(
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
    let compiled = compiler.compile_family_circuit(
        cs_output,
        max_bytecode_size_in_words,
        0,
        trace_len_log2,
        false,
    );

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
    let compiled = compiler.compile_delegation_circuit(cs_output, trace_len_log2, true);

    compiled
}

pub fn compile_delegation_circuit_into_gkr_without_caches<F: PrimeField>(
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
    let compiled = compiler.compile_delegation_circuit(cs_output, trace_len_log2, false);

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

/// Test-only fixture writer shared by the per-circuit codegen-IR generator
/// tests: lower a compiled GKR artifact to the codegen IR, verify it, and
/// write pretty JSON to `filename` (relative to the crate root).
#[cfg(test)]
pub(crate) fn write_codegen_ir_fixture<F: PrimeField + PartialEq>(
    artifact: &GKRCircuitArtifact<F>,
    filename: &str,
) {
    let circuit = lower::<F>(artifact).expect("lower must succeed");
    circuit.verify().expect("lowered circuit must verify");
    let json = to_json_string(&circuit).expect("to_json_string must succeed");
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(filename);
    std::fs::write(&path, &json).expect("write json");
    println!(
        "wrote {} ({} layers, {} bytes)",
        path.display(),
        circuit.layers.len(),
        json.len()
    );
}
