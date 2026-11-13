module
public import Human.Compiler.NativeArithmetic
public import Proven.GKRCompiler.Arithmetic
public import Proven.GKRProtocol.BaseAssignment
public import Proven.GKRProtocol.CleanArithmetic

@[expose] public section
namespace Airbender.Compiler.NativeBridge
open NativeArithmetic
set_option warningAsError true

/-- A native scalar cache or native gate retains its complete imported relation. -/
inductive Clause where
  | cache (output : GKRAddress) (relation : GKRCacheRelation)
  | gate (relation : GKRRelation)

/-- Native residuals use the sparse relation, without its structured helper expression. -/
def Clause.residual (clause : Clause) (physical : GKRAddress → F) : F :=
  match clause with
  | .cache output (.SingleColumnLookup input _) => physical output - linear input.input physical
  | .gate (.LinearBaseFieldRelation input output) => physical output - linear input physical
  | .gate (.MaxQuadratic input _ output) => physical output - quadratic input physical
  | .gate (.EnforceSingleMaxQuadraticConstraint input _) => quadratic input physical
  | .gate (.CopyInBaseField input output) => physical output - physical input
  | .gate (.MaterializeSingleLookupInput input output _) => physical output - linear input.input physical
  | _ => 0

/-- The scalar relation forms used by the cached arithmetic model. -/
def Clause.isBase : Clause → Bool
  | .cache _ (.SingleColumnLookup _ _) => true
  | .gate (.LinearBaseFieldRelation _ _) | .gate (.MaxQuadratic _ _ _) |
    .gate (.EnforceSingleMaxQuadraticConstraint _ _) | .gate (.CopyInBaseField _ _) |
    .gate (.MaterializeSingleLookupInput _ _ _) => true
  | _ => false

/-- Retain native cache order, then native gate order, as in the arithmetic capture. -/
def clauses (circuit : Circuit) : List Clause :=
  circuit.layers.toList.flatMap (fun layer => layer.cached_relations.toList.map fun entry => .cache entry.1 entry.2) ++
    circuit.layers.toList.flatMap (fun layer => (layer.gates ++ layer.gates_with_external_connections).toList.map
      fun gate => .gate gate.enforced_relation)

/-- Every native scalar arithmetic relation, including scalar caches. -/
def baseClauses (circuit : Circuit) := (clauses circuit).filter Clause.isBase

/-- A native cache equation implies its scalar residual equation. -/
theorem cache_zero (output : GKRAddress) (relation : GKRCacheRelation) (physical : GKRAddress → F)
    (accepted : CacheHolds output relation physical) : (Clause.cache output relation).residual physical = 0 := by
  cases relation <;> first | rfl | exact sub_eq_zero.mpr accepted

/-- A native base gate equation implies its scalar residual equation. -/
theorem gate_zero (relation : GKRRelation) (physical : GKRAddress → F)
    (accepted : GateHolds relation physical) : (Clause.gate relation).residual physical = 0 := by
  cases relation <;> first | rfl | exact accepted | exact sub_eq_zero.mpr accepted

/-- The public native gate predicate supplies every retained sparse scalar equation. -/
theorem clauses_zero {circuit : Circuit} {physical : GKRAddress → F} (accepted : Holds circuit physical) :
    ∀ clause ∈ baseClauses circuit, clause.residual physical = 0 := by
  intro clause member
  have present := List.mem_of_mem_filter member
  rcases List.mem_append.mp present with cache | gate
  · obtain ⟨layer, included, present⟩ := List.mem_flatMap.mp cache
    obtain ⟨entry, entryPresent, rfl⟩ := List.mem_map.mp present
    exact cache_zero entry.1 entry.2 physical ((accepted layer (by simpa using included)).1 entry (by simpa using entryPresent))
  · obtain ⟨layer, included, present⟩ := List.mem_flatMap.mp gate
    obtain ⟨entry, entryPresent, rfl⟩ := List.mem_map.mp present
    exact gate_zero entry.enforced_relation physical ((accepted layer (by simpa using included)).2 entry (by simpa using entryPresent))

/-- Evaluate the retained sparse input tree before polynomial normalization. -/
def sparseResidual (gate : ArithmeticGate n F) (values : Fin n → F) : F :=
  match gate with
  | .assertZero input _ => input.value values
  | .define output input _ => values output - input.value values
  | .copy output input => values output - values input

/-- The polynomial checker proves equality of sparse and structured evaluations. -/
theorem sparse_checked {gate : ArithmeticGate n F} (checked : gate.check = true) (values : Fin n → F) :
    sparseResidual gate values = gate.expressionResidual values := by
  have value := gate.checked_value checked values
  have same : evaluate values gate.inputResidual = sparseResidual gate values := by
    cases gate <;> simp only [ArithmeticGate.inputResidual, sparseResidual, evaluate_add,
      evaluate_atom, evaluate_negate, Expression.polynomial_value, sub_eq_add_neg]
  exact same.symm.trans value

/-- Read a scalar cache equation from its actual layer and array position. -/
theorem cache_at {circuit : Circuit} {physical : GKRAddress → F} (accepted : Holds circuit physical)
    (layer : Fin circuit.layers.size)
    (index : Fin circuit.layers[layer].cached_relations.size) :
    (Clause.cache circuit.layers[layer].cached_relations[index].1
      circuit.layers[layer].cached_relations[index].2).residual physical = 0 :=
  cache_zero _ _ physical ((accepted _ (Array.getElem_mem _)).1 _ (Array.getElem_mem _))

/-- Read a gate equation from its actual layer and array position. -/
theorem gate_at {circuit : Circuit} {physical : GKRAddress → F} (accepted : Holds circuit physical)
    (layer : Fin circuit.layers.size)
    (index : Fin (circuit.layers[layer].gates ++ circuit.layers[layer].gates_with_external_connections).size) :
    (Clause.gate (circuit.layers[layer].gates ++
      circuit.layers[layer].gates_with_external_connections)[index].enforced_relation).residual physical = 0 :=
  gate_zero _ physical ((accepted _ (Array.getElem_mem _)).2 _ (Array.getElem_mem _))

/-- Prepend one gate equation to a complete batch. -/
theorem cons_holds {head : ArithmeticGate n F} {tail : List (ArithmeticGate n F)} {values : Fin n → F}
    (first : head.expressionResidual values = 0)
    (rest : ∀ gate ∈ tail, gate.expressionResidual values = 0) :
    ∀ gate ∈ head :: tail, gate.expressionResidual values = 0 := by
  intro gate member
  rcases List.mem_cons.mp member with rfl | included
  · exact first
  · exact rest gate included

/-- Join complete batches without changing their order. -/
theorem append_holds {first rest : List (ArithmeticGate n F)} {values : Fin n → F}
    (left : ∀ gate ∈ first, gate.expressionResidual values = 0)
    (right : ∀ gate ∈ rest, gate.expressionResidual values = 0) :
    ∀ gate ∈ first ++ rest, gate.expressionResidual values = 0 := by
  intro gate member
  exact (List.mem_append.mp member).elim (left gate) (right gate)

/-- Expression evaluation depends only on the listed input columns. -/
theorem eval_congr (expression : Airbender.Expression F) (left right : Environment F)
    (same : ∀ index ∈ CleanExpression.inputs expression, left.get index = right.get index) :
    expression.eval left = expression.eval right := by
  induction expression with
  | var wire => exact same wire.index List.mem_cons_self
  | const _ => rfl
  | add first rest ihFirst ihRest =>
    exact congrArg₂ (· + ·) (ihFirst (fun i h => same i (List.mem_append_left _ h)))
      (ihRest (fun i h => same i (List.mem_append_right _ h)))
  | mul first rest ihFirst ihRest =>
    exact congrArg₂ (· * ·) (ihFirst (fun i h => same i (List.mem_append_left _ h)))
      (ihRest (fun i h => same i (List.mem_append_right _ h)))

/-- Transfer a complete assertion list through its checked variable scope. -/
theorem assertions_transport (expressions : List (Airbender.Expression F))
    (left right : Environment F) (limit : Nat)
    (scope : expressions.all (fun expression =>
      (CleanExpression.inputs expression).all (fun index => decide (index < limit))) = true)
    (same : ∀ index < limit, left.get index = right.get index)
    (holds : FlatOperation.ConstraintsHoldFlat left (expressions.map FlatOperation.assert)) :
    FlatOperation.ConstraintsHoldFlat right (expressions.map FlatOperation.assert) := by
  induction expressions with
  | nil => trivial
  | cons head tail ih =>
    have checks := Bool.and_eq_true_iff.mp scope
    refine ⟨?_, ih checks.2 holds.2⟩
    have equal := eval_congr head left right (fun index member =>
      same index (of_decide_eq_true (List.all_eq_true.mp checks.1 index member)))
    exact equal.symm.trans holds.1

/-- Prepend one checked public placement to a finite placement batch. -/
theorem cons_placements {head : Nat} {tail : List Nat} {left right : Nat → F}
    (first : left head = right head) (rest : ∀ index ∈ tail, left index = right index) :
    ∀ index ∈ head :: tail, left index = right index := by
  intro index member
  exact (List.mem_cons.mp member).elim (fun equal => equal ▸ first) (rest index)

/-- Join complete public placement batches. -/
theorem append_placements {first rest : List Nat} {left right : Nat → F}
    (a : ∀ index ∈ first, left index = right index) (b : ∀ index ∈ rest, left index = right index) :
    ∀ index ∈ first ++ rest, left index = right index := by
  intro index member
  exact (List.mem_append.mp member).elim (a index) (b index)

end Airbender.Compiler.NativeBridge
