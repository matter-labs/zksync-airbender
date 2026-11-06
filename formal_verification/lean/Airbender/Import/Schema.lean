import Airbender.Import.Mersenne31

namespace Airbender
open Lean

/-- Native v2 physical column addresses, not GKR layer addresses. -/
inductive ColumnAddress where
  | WitnessSubtree : Nat → ColumnAddress
  | MemorySubtree : Nat → ColumnAddress
  | SetupSubtree : Nat → ColumnAddress
  | OptimizedOut : Nat → ColumnAddress
  deriving Repr, DecidableEq, FromJson, ToJson

/-- num_elements counts WIDTH-sized groups in Rust ColumnSet<WIDTH>. -/
structure ColumnSet where
  start : Nat
  num_elements : Nat
  deriving Repr, FromJson, ToJson

structure CompiledDegree1Constraint where
  linear_terms : Array (Coefficient × ColumnAddress)
  constant_term : Coefficient
  deriving Repr, FromJson, ToJson

structure CompiledDegree2Constraint where
  quadratic_terms : Array (Triple Coefficient ColumnAddress ColumnAddress)
  linear_terms : Array (Coefficient × ColumnAddress)
  constant_term : Coefficient
  deriving Repr, FromJson, ToJson

inductive LookupExpression where
  | Variable : ColumnAddress → LookupExpression
  | Expression : CompiledDegree1Constraint → LookupExpression
  deriving Repr, FromJson, ToJson

/-- Native fixed tables consumed by the checked memory/control/byte profiles. -/
inductive FixedTableId where
  | RomAddressSpaceSeparator
  | RomRead
  | ConditionalJmpBranchSlt
  | JumpCleanupOffset
  | RangeCheckSmall
  | MemoryGetOffsetAndMaskWithTrap
  | U16GetSignAndHighByte
  deriving Repr, DecidableEq, FromJson, ToJson

/-- Native constants and physical witness selectors. Variable selectors are
    accepted only by the concrete shift/binop or subword profile checked in Parse. -/
inductive FixedTableIndex where
  | Constant : FixedTableId → FixedTableIndex
  | Variable : ColumnAddress → FixedTableIndex
  deriving Repr, DecidableEq, FromJson

structure FixedLookup where
  input_columns : Array LookupExpression
  table_index : FixedTableIndex
  deriving Repr, FromJson

/-- Fail closed for features without an emitter; do not silently omit obligations. -/
structure EmptyArray where
  deriving Repr

instance : FromJson EmptyArray where
  fromJson? j := do
    unless (← j.getArr?).isEmpty do
      throw "unsupported nonempty inter-row state linkage"
    pure ⟨⟩

structure WitnessSubtree where
  total_width : Nat
  boolean_vars_columns_range : ColumnSet
  range_check_8_columns : ColumnSet
  range_check_16_columns : ColumnSet
  width_3_lookups : Array FixedLookup
  range_check_16_lookup_expressions : Array LookupExpression
  timestamp_range_check_lookup_expressions : Array LookupExpression
  deriving Repr, FromJson

structure RegisterOnlyAccessAddress where
  register_index : ColumnSet
  deriving Repr, FromJson

structure RegisterOrRamAccessAddress where
  is_register : ColumnSet
  address : ColumnSet
  deriving Repr, FromJson

inductive ShuffleRamAddress where
  | RegisterOnly : RegisterOnlyAccessAddress → ShuffleRamAddress
  | RegisterOrRam : RegisterOrRamAccessAddress → ShuffleRamAddress
  deriving Repr, FromJson

structure ShuffleRamQueryReadColumns where
  in_cycle_write_index : U32
  address : ShuffleRamAddress
  read_timestamp : ColumnSet
  read_value : ColumnSet
  deriving Repr, FromJson

structure ShuffleRamQueryWriteColumns where
  in_cycle_write_index : U32
  address : ShuffleRamAddress
  read_timestamp : ColumnSet
  read_value : ColumnSet
  write_value : ColumnSet
  deriving Repr, FromJson

def ShuffleRamQueryWriteColumns.toShuffleRamQueryReadColumns
    (q : ShuffleRamQueryWriteColumns) : ShuffleRamQueryReadColumns :=
  ⟨q.in_cycle_write_index, q.address, q.read_timestamp, q.read_value⟩

inductive ShuffleRamQueryColumns where
  | Readonly : ShuffleRamQueryReadColumns → ShuffleRamQueryColumns
  | Write : ShuffleRamQueryWriteColumns → ShuffleRamQueryColumns
  deriving Repr, FromJson

structure MachineStatePermutationVariables where
  pc : ColumnSet
  timestamp : ColumnSet
  deriving Repr, FromJson

structure IntermediateStatePermutationVariables where
  execute : ColumnSet
  pc : ColumnSet
  timestamp : ColumnSet
  rs1_index : ColumnSet
  rs2_index : ColumnAddress
  rd_index : ColumnAddress
  decoder_witness_is_in_memory : Bool
  rd_is_zero : ColumnSet
  imm : ColumnSet
  funct3 : ColumnSet
  funct7 : ColumnSet
  circuit_family : ColumnSet
  circuit_family_extra_mask : ColumnAddress
  deriving Repr, FromJson

/-- Physical lazy-init/teardown columns. Imported descriptors do not establish
    sorted initialization windows, public values or argument enforcement. -/
structure InitTeardownColumns where
  lazy_init_addresses_columns : ColumnSet
  lazy_teardown_values_columns : ColumnSet
  lazy_teardown_timestamps_columns : ColumnSet
  deriving Repr, FromJson

/-- Actual caller request fields and issue-clock offset. Worker participation
    and cancellation are separate obligations, not consequences of this record. -/
structure DelegationRequestColumns where
  multiplicity : ColumnSet
  delegation_type : ColumnSet
  abi_mem_offset_high : ColumnSet
  in_cycle_write_index : U32
  deriving Repr, FromJson

/-- An unsupported active processor layout must never disappear on parsing. -/
structure UnsupportedProcessor where
  deriving Repr

instance : FromJson UnsupportedProcessor where
  fromJson? _ := .error "unsupported native delegation processor layout"

structure LazyInitAddressAux where
  aux_low_high : Array ColumnAddress
  intermediate_borrow : ColumnAddress
  final_borrow : ColumnAddress
  deriving Repr, FromJson

structure InactiveBatchedTimestampAux where
  predicate : ColumnAddress
  write_timestamp_columns : ColumnSet
  write_timestamp : Array ColumnAddress
  aux_borrow_vars : EmptyArray
  deriving Repr, FromJson

structure InactiveIndirectTimestampAux where
  predicate : ColumnAddress
  write_timestamp_columns : ColumnSet
  write_timestamp : Array ColumnAddress
  aux_borrow_sets : EmptyArray
  deriving Repr, FromJson

/-- Consumed direct shuffle-RAM and state metadata. Batched delegation arguments
    and cryptographic memory/state enforcement are separate milestones. -/
structure MemorySubtree where
  shuffle_ram_inits_and_teardowns : Array InitTeardownColumns
  delegation_request_layout : Option DelegationRequestColumns
  delegation_processor_layout : Option UnsupportedProcessor
  batched_ram_accesses : EmptyArray
  register_and_indirect_accesses : EmptyArray
  total_width : Nat
  shuffle_ram_access_sets : Array ShuffleRamQueryColumns
  machine_state_layout : Option MachineStatePermutationVariables
  intermediate_state_layout : Option IntermediateStatePermutationVariables
  deriving Repr, FromJson

structure SetupLayout where
  timestamp_setup_columns : ColumnSet
  range_check_16_setup_column : ColumnSet
  timestamp_range_check_setup_column : ColumnSet
  generic_lookup_setup_columns : ColumnSet
  preprocessed_decoder_setup_columns : ColumnSet
  total_width : Nat
  deriving Repr, FromJson

/-- Preserve the native stage-two descriptor without claiming its argument
    polynomials or commitments have been interpreted by local-row intake. -/
structure RetainedStageTwo where
  raw : Json

instance : FromJson RetainedStageTwo where
  fromJson? raw := do
    let _ ← raw.getObj?
    pure ⟨raw⟩
instance : Repr RetainedStageTwo := ⟨fun stage _ => repr stage.raw.compress⟩

/-- Consumed projection of CompiledCircuitArtifact at the pinned v2 revision.
    Stage-two arguments and public boundaries are separate from local row claims. -/
structure Circuit where
  /-- Retained verbatim at the separate stage-two/cryptographic boundary. -/
  stage_2_layout : RetainedStageTwo
  public_inputs : EmptyArray
  lazy_init_address_aux_vars : Array LazyInitAddressAux
  batched_memory_access_timestamp_comparison_aux_vars : InactiveBatchedTimestampAux
  register_and_indirect_access_timestamp_comparison_aux_vars : InactiveIndirectTimestampAux
  witness_layout : WitnessSubtree
  memory_layout : MemorySubtree
  setup_layout : SetupLayout
  executor_family_decoder_table_size : Nat
  trace_len : Nat
  table_offsets : Array Nat
  total_tables_size : Nat
  degree_2_constraints : Array CompiledDegree2Constraint
  degree_1_constraints : Array CompiledDegree1Constraint
  state_linkage_constraints : EmptyArray
  scratch_space_size_for_witness_gen : Nat
  variable_mapping : ObjectMap Nat ColumnAddress
  memory_queries_timestamp_comparison_aux_vars : Array ColumnAddress
  executor_family_circuit_next_timestamp_aux_var : Option ColumnAddress
  deriving Repr, FromJson

inductive Expr where
  | Constant : Coefficient → Expr
  | Var : Nat → Expr
  | Sum : Array Expr → Expr
  | Product : Array Expr → Expr
  deriving Repr

end Airbender
