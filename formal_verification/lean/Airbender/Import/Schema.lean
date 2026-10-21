import Airbender.Import.BabyBear

/- Native mirror of the v3 Rust serde schema at commit 4518846625730fabc4cd83744d4bd983a5e42b97.
   Coefficients are fixed to BabyBear Montgomery encoding. No fields are opaque JSON. -/
namespace Airbender
open Lean

structure ColumnRange where
  start : Nat
  «end» : Nat
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr_layers.rs`, `OutputType`. -/
inductive OutputType where
  | PermutationProduct
  | Lookup16Bits
  | LookupTimestamps
  | GenericLookup
  | InitsAndTeardownsProduct
  deriving Repr, FromJson, ToJson

instance : ObjectKey OutputType where
  decode s := fromJson? (.str s)
  encode k := (toJson k).getStr?.toOption.getD ""

/-- Source: `cs/src/definitions/gkr_layers.rs`, `VirtualSetupPoly`. -/
inductive VirtualSetupPoly where
  | RangeCheck16Bits
  | RangeCheckTimestamp
  | InitsAndTeardownsLow
  | InitsAndTeardownsHigh
  deriving Repr, DecidableEq, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr_layers.rs`, `GKRAddress`. -/
inductive GKRAddress where
  | BaseLayerWitness : Nat → GKRAddress
  | BaseLayerMemory : Nat → GKRAddress
  | InnerLayer (layer : Nat) (offset : Nat)
  | Setup : Nat → GKRAddress
  | VirtualSetup : VirtualSetupPoly → GKRAddress
  | ScratchSpace : Nat → GKRAddress
  | Cached (layer : Nat) (offset : Nat)
  deriving Repr, DecidableEq, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/utils.rs`, `LinearRelation`. -/
structure LinearRelation where
  linear_terms : (Array (Coefficient × GKRAddress))
  constant : Coefficient
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/lookup.rs`, `SingleColumnLookupRelation`. -/
structure SingleColumnLookupRelation where
  input : LinearRelation
  lookup_set_index : Nat
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/lookup.rs`, `VectorLookupRelation`. -/
structure VectorLookupRelation where
  columns : (Array LinearRelation)
  lookup_set_index : Nat
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `CompiledMaxQuadraticGKRRelation`. -/
structure CompiledMaxQuadraticGKRRelation where
  quadratic_terms : (Array (GKRAddress × (Array (Coefficient × GKRAddress))))
  linear_terms : (Array (Coefficient × GKRAddress))
  constant : Coefficient
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `CompiledAddressSpaceRelationStrict`. -/
inductive CompiledAddressSpaceRelationStrict where
  | Constant : U32 → CompiledAddressSpaceRelationStrict
  | IsRegister : Nat → CompiledAddressSpaceRelationStrict
  | IsRam : Nat → CompiledAddressSpaceRelationStrict
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `CompiledAddressStrict`. -/
inductive CompiledAddressStrict where
  | ConstantU16 : U16 → CompiledAddressStrict
  | Constant : U32 → CompiledAddressStrict
  | U16Space : Nat → CompiledAddressStrict
  | U32Space : (Fixed 2 Nat) → CompiledAddressStrict
  | U32SpaceSpecialIndirect (low_base : Nat) (low_dynamic_offset : (Option (U16 × Nat))) (low_offset : U32) (high : Nat)
  | U32SpaceGeneric : (Fixed 2 ((Array ((BoundedNat 18446744073709551616) × Nat)) × (BoundedNat 18446744073709551616))) → CompiledAddressStrict
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `CompiledMemoryTimestamp`. -/
inductive CompiledMemoryTimestamp where
  | Zero
  | Normal : (Fixed 2 Nat) → CompiledMemoryTimestamp
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamWordRepresentation`. -/
inductive RamWordRepresentation where
  | Zero
  | U16Limbs : (Fixed 2 Nat) → RamWordRepresentation
  | U8Limbs : (Fixed 4 Nat) → RamWordRepresentation
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `SpecialMemoryContributionRelation`. -/
structure SpecialMemoryContributionRelation where
  address_space : CompiledAddressSpaceRelationStrict
  address : CompiledAddressStrict
  timestamp : CompiledMemoryTimestamp
  value : RamWordRepresentation
  timestamp_offset : U32
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `MaxQuadraticConstraintsGKRRelation`. -/
structure MaxQuadraticConstraintsGKRRelation where
  quadratic_terms : (Array ((GKRAddress × GKRAddress) × (Array (Coefficient × Nat))))
  linear_terms : (Array (GKRAddress × (Array (Coefficient × Nat))))
  constants : (Array (Coefficient × Nat))
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `InitsOrTeardownsTimestampAndValue`. -/
inductive InitsOrTeardownsTimestampAndValue where
  | Init
  | Teardown (lhs_timestamp : (Fixed 2 Nat)) (lhs_value : (Fixed 2 Nat)) (rhs_timestamp : (Fixed 2 Nat)) (rhs_value : (Fixed 2 Nat))
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `StructuredExpression`. -/
inductive StructuredExpression where
  | Constant : Coefficient → StructuredExpression
  | Place : GKRAddress → StructuredExpression
  | Sum : (Array StructuredExpression) → StructuredExpression
  | Product : (Array StructuredExpression) → StructuredExpression
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `GKRRelation`. -/
inductive GKRRelation where
  | LinearBaseFieldRelation (input : LinearRelation) (output : GKRAddress)
  | MaxQuadratic (input : CompiledMaxQuadraticGKRRelation) (expression : StructuredExpression) (output : GKRAddress)
  | EnforceSingleMaxQuadraticConstraint (input : CompiledMaxQuadraticGKRRelation) (expression : StructuredExpression)
  | EnforceConstraintsMaxQuadratic (input : MaxQuadraticConstraintsGKRRelation)
  | CopyInBaseField (input : GKRAddress) (output : GKRAddress)
  | CopyInExtensionField (input : GKRAddress) (output : GKRAddress)
  | InitialGrandProductFromCaches (input : (Fixed 2 GKRAddress)) (output : GKRAddress)
  | InitialGrandProductWithoutCaches (input : (Fixed 2 SpecialMemoryContributionRelation)) (output : GKRAddress)
  | UnbalancedGrandProductWithCache (scalar : GKRAddress) (input : GKRAddress) (output : GKRAddress)
  | MaterializeGrandProductTermExpression (input : SpecialMemoryContributionRelation) (output : GKRAddress)
  | TrivialProduct (input : (Fixed 2 GKRAddress)) (output : GKRAddress)
  | MaskIntoIdentityProduct (input : GKRAddress) (mask : GKRAddress) (output : GKRAddress)
  | MaterializeSingleLookupInput (input : SingleColumnLookupRelation) (output : GKRAddress) (range_check_width : U32)
  | MaterializedVectorLookupInput (input : VectorLookupRelation) (output : GKRAddress)
  | LookupWithCachedDensAndSetup (input : (Fixed 2 GKRAddress)) (setup : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupWithDensAndSetupExpressions (input : (GKRAddress × VectorLookupRelation)) (setup : (GKRAddress × (Array GKRAddress))) (output : (Fixed 2 GKRAddress))
  | LookupPairFromBaseInputs (input : (Fixed 2 SingleColumnLookupRelation)) (output : (Fixed 2 GKRAddress)) (range_check_width : U32)
  | LookupPairFromMaterializedBaseInputs (input : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupFromBaseInputsWithSetup (input : SingleColumnLookupRelation) (setup : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress)) (range_check_width : U32)
  | LookupFromMaterializedBaseInputWithSetup (input : GKRAddress) (setup : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupUnbalancedPairWithMaterializedBaseInputs (input : (Fixed 2 GKRAddress)) (remainder : GKRAddress) (output : (Fixed 2 GKRAddress))
  | LookupPairFromVectorInputs (input : (Fixed 2 VectorLookupRelation)) (output : (Fixed 2 GKRAddress))
  | LookupPairFromMaterializedVectorInputs (input : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupFromVectorInputWithSetup (input : VectorLookupRelation) (setup : (GKRAddress × (Array GKRAddress))) (output : (Fixed 2 GKRAddress))
  | LookupFromMaterializedVectorInputWithSetup (input : GKRAddress) (setup : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupPairFromCachedVectorInputs (input : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupUnbalancedPairWithVectorInputs (input : (Fixed 2 GKRAddress)) (remainder : VectorLookupRelation) (output : (Fixed 2 GKRAddress))
  | LookupUnbalancedPairWithMaterializedVectorInputs (input : (Fixed 2 GKRAddress)) (remainder : GKRAddress) (output : (Fixed 2 GKRAddress))
  | AggregateLookupRationalPair (input : (Fixed 2 (Fixed 2 GKRAddress))) (output : (Fixed 2 GKRAddress))
  | InitsOrTeardownsInitialPair (timestamp_and_value : InitsOrTeardownsTimestampAndValue) (setup : (Fixed 2 GKRAddress)) (output : GKRAddress) (set_idxes : (Fixed 2 Nat))
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `GKRCacheRelation`. -/
inductive GKRCacheRelation where
  | SingleColumnLookup (relation : SingleColumnLookupRelation) (range_check_width : Nat)
  | VectorizedLookup : VectorLookupRelation → GKRCacheRelation
  | MemoryTuple : SpecialMemoryContributionRelation → GKRCacheRelation
  | VectorizedLookupSetup : (Array GKRAddress) → GKRCacheRelation
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `GateArtifacts`. -/
structure GateArtifacts where
  output_layer : Nat
  enforced_relation : GKRRelation
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamAuxComparisonSet`. -/
structure RamAuxComparisonSet where
  intermediate_borrow : GKRAddress
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/layout.rs`, `GKRAuxLayoutData`. -/
structure GKRAuxLayoutData where
  shuffle_ram_timestamp_comparison_aux_vars : (Array RamAuxComparisonSet)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/layout.rs`, `GKRLayerDescription`. -/
structure GKRLayerDescription where
  layer : Nat
  gates_with_external_connections : (Array GateArtifacts)
  cached_relations : (Array (GKRAddress × GKRCacheRelation))
  gates : (Array GateArtifacts)
  intermediate_layer_width : (Option Nat)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RegisterOnlyAccessAddress`. -/
structure RegisterOnlyAccessAddress where
  register_index : Nat
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RegisterOrRamAddressSpace`. -/
inductive RegisterOrRamAddressSpace where
  | RegisterAddressSpace : Nat → RegisterOrRamAddressSpace
  | RamAddressSpace : Nat → RegisterOrRamAddressSpace
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RegisterOrRamAccessAddress`. -/
structure RegisterOrRamAccessAddress where
  address_space : RegisterOrRamAddressSpace
  address : (Fixed 2 Nat)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `IndirectRamAccessAddress`. -/
structure IndirectRamAccessAddress where
  base_register_value : (Fixed 2 Nat)
  base_register_index : U16
  constant_offset : U16
  indirect_access_idx_for_register : Nat
  variable_offset : (Option (U16 × Nat))
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamAddress`. -/
inductive RamAddress where
  | ConstantRegister : U16 → RamAddress
  | RegisterOnly : RegisterOnlyAccessAddress → RamAddress
  | RegisterOrRam : RegisterOrRamAccessAddress → RamAddress
  | IndirectRam : IndirectRamAccessAddress → RamAddress
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamReadQuery`. -/
structure RamReadQuery where
  in_cycle_write_index : U32
  address : RamAddress
  read_timestamp : (Fixed 2 Nat)
  read_value : RamWordRepresentation
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamWriteQuery`. -/
structure RamWriteQuery where
  in_cycle_write_index : U32
  address : RamAddress
  read_timestamp : (Fixed 2 Nat)
  read_value : RamWordRepresentation
  write_value : RamWordRepresentation
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamQuery`. -/
inductive RamQuery where
  | Readonly : RamReadQuery → RamQuery
  | Write : RamWriteQuery → RamQuery
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/mod.rs`, `GKRMachineState`. -/
structure GKRMachineState where
  pc : (Fixed 2 Nat)
  timestamp : (Fixed 2 Nat)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/mod.rs`, `MachineStatePermutationDescription`. -/
structure MachineStatePermutationDescription where
  execute : Nat
  initial_state : GKRMachineState
  final_state : GKRMachineState
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/mod.rs`, `CompiledDelegationCircuitState`. -/
structure CompiledDelegationCircuitState where
  execute : Nat
  invocation_timestamp : (Fixed 2 Nat)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/mod.rs`, `DecoderPlacementDescription`. -/
structure DecoderPlacementDescription where
  rs1_index : Nat
  rs2_index : GKRAddress
  rd_index : GKRAddress
  circuit_family_mask_bits : (Array GKRAddress)
  decoder_witness_is_in_memory : Bool
  imm : (Fixed 2 Nat)
  funct3 : (Option Nat)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/mod.rs`, `GKRMemoryLayout`. -/
structure GKRMemoryLayout where
  ram_access_sets : (Array RamQuery)
  machine_state : (Option MachineStatePermutationDescription)
  delegation_state : (Option CompiledDelegationCircuitState)
  decoder_input : (Option DecoderPlacementDescription)
  indirect_access_variable_offsets : (Array Nat)
  teardown_sets : (Array ((Fixed 2 GKRAddress) × (Fixed 2 GKRAddress)))
  total_width : Nat
  inits_and_teardowns_word_bits : (Option U32)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/gkr/mod.rs`, `GKRWitnessLayout`. -/
structure GKRWitnessLayout where
  multiplicities_columns_for_range_check_16 : ColumnRange
  multiplicities_columns_for_timestamp_range_check : ColumnRange
  multiplicities_columns_for_generic_lookup : ColumnRange
  total_width : Nat
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/constraints.rs`, `Degree1Constraint`. -/
structure Degree1Constraint where
  linear_terms : (Array (Coefficient × Nat))
  constant_term : Coefficient
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/definitions/constraints.rs`, `Degree2Constraint`. -/
structure Degree2Constraint where
  quadratic_terms : (Array (Triple Coefficient Nat Nat))
  linear_terms : (Array (Coefficient × Nat))
  constant_term : Coefficient
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/constraint.rs`, `Term`. -/
inductive Term where
  | Constant : Coefficient → Term
  | Expression (coeff : Coefficient) (inner : (Fixed 4 Nat)) (degree : Nat)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/constraint.rs`, `Constraint`. -/
structure Constraint where
  terms : (Array Term)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/structured_expr.rs`, `Expr`. -/
inductive Expr where
  | Constant : Coefficient → Expr
  | Var : Nat → Expr
  | Sum : (Array Expr) → Expr
  | Product : (Array Expr) → Expr
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/structured_expr.rs`, `StructuredStatement`. -/
inductive StructuredStatement where
  | AssertZero (expr : Expr) (compiled_constraint : Constraint) (prevent_optimizations : Bool)
  | Define (dst : Nat) (compiled_constraint : Constraint) (expr : Expr) (output_layer : Nat)
  deriving Repr, FromJson, ToJson

/-- Source: `cs/src/gkr_compiler/mod.rs`, `GKRCircuitArtifact`. -/
structure GKRCircuitArtifact where
  trace_len : Nat
  table_offsets : (Array U32)
  total_tables_size : Nat
  offset_for_decoder_table : Nat
  has_decoder_lookup : Bool
  layers : (Array GKRLayerDescription)
  global_output_map : (ObjectMap OutputType (Array GKRAddress))
  memory_layout : GKRMemoryLayout
  witness_layout : GKRWitnessLayout
  scratch_space_size : Nat
  num_generic_lookups : Nat
  placement_data : (ObjectMap Nat GKRAddress)
  generic_lookup_tables_width : Nat
  decode_table_columns_mask : (Array Bool)
  tables_ids_in_generic_lookups : Bool
  /-- Serialized field value used in every physical setup-tail column;
      absence retains the native zero-padding meaning. -/
  generic_lookup_padding : Option Coefficient := none
  degree_2_constraints : (Array Degree2Constraint)
  degree_1_constraints : (Array Degree1Constraint)
  structured_statements : (Array StructuredStatement)
  generic_lookups : (Array VectorLookupRelation)
  range_check_16_lookup_expressions : (Array SingleColumnLookupRelation)
  timestamp_range_check_lookup_expressions : (Array SingleColumnLookupRelation)
  variable_names : (ObjectMap Nat String)
  scratch_space_mapping : (Array (GKRAddress × Nat))
  scratch_space_mapping_rev : (ObjectMap Nat GKRAddress)
  aux_layout_data : GKRAuxLayoutData
  _marker : JsonNull
  deriving Repr, FromJson, ToJson

abbrev Circuit := GKRCircuitArtifact

end Airbender
