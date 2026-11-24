module
public import Proven.Compiler.NativeBridge

@[expose] public section
namespace Airbender.Compiler.NativeBridge
open NativeArithmetic
set_option warningAsError true

/-- Every variable used by an expression lies in the captured source domain. -/
def expressionScope (limit : Nat) (expression : Airbender.Expression F) : Bool :=
  (CleanExpression.inputs expression).all (fun index => decide (index < limit))

/-- The source scope covers assertion and lookup operands. -/
def operationScope (limit : Nat) : FlatOperation F → Bool
  | .assert expression => expressionScope limit expression
  | .lookup lookup => lookup.entry.toList.all (expressionScope limit)

/-- A scoped expression reads only the shared physical-to-logical placements. -/
theorem expression_transport (expression : Airbender.Expression F) (left right : Environment F)
    (limit : Nat) (scope : expressionScope limit expression = true)
    (same : ∀ index < limit, left.get index = right.get index) :
    expression.eval left = expression.eval right :=
  eval_congr expression left right (fun index member =>
    same index (of_decide_eq_true (List.all_eq_true.mp scope index member)))

/-- A lookup retains its table and every evaluated field under scoped placement agreement. -/
theorem lookup_transport (lookup : Lookup F) (left right : Environment F)
    (limit : Nat) (scope : lookup.entry.toList.all (expressionScope limit) = true)
    (same : ∀ index < limit, left.get index = right.get index)
    (data : left.data = right.data) (holds : lookup.Contains left) : lookup.Contains right := by
  have fields : lookup.entry.map left = lookup.entry.map right := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    apply expression_transport _ left right limit
    · apply List.all_eq_true.mp scope
      simp
    · exact same
  unfold Lookup.Contains at *
  rw [← data, ← fields]
  exact holds

/-- All imported row constraints keep their meaning under checked source placements. -/
theorem constraints_transport (operations : List (FlatOperation F)) (left right : Environment F)
    (limit : Nat) (scope : operations.all (operationScope limit) = true)
    (same : ∀ index < limit, left.get index = right.get index) (data : left.data = right.data)
    (holds : FlatOperation.ConstraintsHoldFlat left operations) :
    FlatOperation.ConstraintsHoldFlat right operations := by
  induction operations with
  | nil => trivial
  | cons head tail ih =>
    have checks := Bool.and_eq_true_iff.mp scope
    cases head with
    | assert expression =>
      exact ⟨(expression_transport expression left right limit checks.1 same).symm.trans holds.1,
        ih checks.2 holds.2⟩
    | lookup lookup =>
      exact ⟨lookup_transport lookup left right limit checks.1 same data holds.1,
        ih checks.2 holds.2⟩

end Airbender.Compiler.NativeBridge
