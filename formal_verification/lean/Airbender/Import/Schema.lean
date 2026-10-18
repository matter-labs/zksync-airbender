import Airbender.Import.Mersenne31

namespace Airbender
open Lean

/-- Native v2 physical column addresses, not GKR layer addresses. -/
inductive ColumnAddress where
  | WitnessSubtree : Nat → ColumnAddress
  | MemorySubtree : Nat → ColumnAddress
  | SetupSubtree : Nat → ColumnAddress
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

/-- Only the two native fixed tables consumed by word-only memory are supported. -/
inductive FixedTableId where
  | RomAddressSpaceSeparator
  | RomRead
  deriving Repr, DecidableEq, FromJson, ToJson

inductive FixedTableIndex where
  | Constant : FixedTableId → FixedTableIndex
  deriving Repr, FromJson

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

/-- Consumed direct shuffle-RAM and state metadata. Batched delegation arguments
    and cryptographic memory/state enforcement are separate milestones. -/
structure MemorySubtree where
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

/-- Consumed projection of CompiledCircuitArtifact at the pinned v2 revision.
    Stage-two arguments and public boundaries are separate from local row claims. -/
structure Circuit where
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
