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

/-- Fail closed for features without an emitter; do not silently omit obligations. -/
structure EmptyArray where
  deriving Repr

instance : FromJson EmptyArray where
  fromJson? j := do
    unless (← j.getArr?).isEmpty do
      throw "unsupported nonempty lookup sets or inter-row state linkage"
    pure ⟨⟩

structure WitnessSubtree where
  total_width : Nat
  boolean_vars_columns_range : ColumnSet
  range_check_8_columns : ColumnSet
  range_check_16_columns : ColumnSet
  width_3_lookups : EmptyArray
  range_check_16_lookup_expressions : Array LookupExpression
  timestamp_range_check_lookup_expressions : Array LookupExpression
  deriving Repr, FromJson

/-- Only widths are needed to resolve local equations. Native memory/state
    arguments are not imported as accepted logical matching in this milestone. -/
structure MemorySubtree where
  total_width : Nat
  deriving Repr, FromJson

structure SetupLayout where
  total_width : Nat
  deriving Repr, FromJson

/-- Consumed projection of CompiledCircuitArtifact at the pinned v2 revision.
    Stage-two arguments and public boundaries are separate from local row claims. -/
structure Circuit where
  witness_layout : WitnessSubtree
  memory_layout : MemorySubtree
  setup_layout : SetupLayout
  degree_2_constraints : Array CompiledDegree2Constraint
  degree_1_constraints : Array CompiledDegree1Constraint
  state_linkage_constraints : EmptyArray
  variable_mapping : ObjectMap Nat ColumnAddress
  deriving Repr, FromJson

inductive Expr where
  | Constant : Coefficient → Expr
  | Var : Nat → Expr
  | Sum : Array Expr → Expr
  | Product : Array Expr → Expr
  deriving Repr

end Airbender
