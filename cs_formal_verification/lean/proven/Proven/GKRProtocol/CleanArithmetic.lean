module
import all Mathlib.Data.List.Sort
public import Proven.GKRCompiler.Arithmetic
public import CleanCore.Circuit.Operations

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler
variable {F : Type}

def CleanExpression.inputs : Airbender.Expression F → List Nat
  | .var wire => [wire.index]
  | .const _ => []
  | .add left right | .mul left right => inputs left ++ inputs right

def CleanExpression.polynomial [CommRing F] (placement : Nat → Fin n) : Airbender.Expression F → Polynomial n F
  | .var wire => atom (placement wire.index)
  | .const value => constant value
  | .add left right => add (polynomial placement left) (polynomial placement right)
  | .mul left right => multiply (polynomial placement left) (polynomial placement right)

theorem CleanExpression.polynomial_value [Field F] (expression : Airbender.Expression F)
    (placement : Nat → Fin n) (values : Fin n → F) (environment : Environment F)
    (same : ∀ index ∈ inputs expression, values (placement index) = environment.get index) :
    evaluate values (polynomial placement expression) = expression.eval environment := by
  induction expression with
  | var wire =>
      simpa only [polynomial, evaluate_atom, Airbender.Expression.eval] using same wire.index List.mem_cons_self
  | const value => exact evaluate_constant values value
  | add left right leftProof rightProof =>
      rw [polynomial, evaluate_add]
      exact congrArg₂ (· + ·)
        (leftProof (fun index member => same index (List.mem_append_left _ member)))
        (rightProof (fun index member => same index (List.mem_append_right _ member)))
  | mul left right leftProof rightProof =>
      rw [polynomial, evaluate_multiply]
      exact congrArg₂ (· * ·)
        (leftProof (fun index member => same index (List.mem_append_left _ member)))
        (rightProof (fun index member => same index (List.mem_append_right _ member)))

/-- A certificate may supply an ideal witness, never a replacement expression.
The expression is the exact Clean AST emitted from the retained post-compiler
structured statement, including its signed coefficient interpretation. -/
theorem CleanExpression.of_combination [Field F] [DecidableEq F]
    (expression : Airbender.Expression F) (placement : Nat → Fin n)
    (relations : List (Polynomial n F)) (witness : Combination relations)
    (checked : equal (polynomial placement expression) (combination relations witness) = true)
    (values : Fin n → F) (holds : Satisfies relations values) (environment : Environment F)
    (same : ∀ index ∈ inputs expression, values (placement index) = environment.get index) :
    expression.eval environment = 0 := by
  exact (polynomial_value expression placement values environment same).symm.trans
    ((equal_sound checked values).trans (combination_zero holds witness))

theorem CleanExpression.assertions_hold [Field F] (expressions : List (Airbender.Expression F))
    (environment : Environment F) (holds : ∀ expression ∈ expressions, expression.eval environment = 0) :
    FlatOperation.ConstraintsHoldFlat environment (expressions.map FlatOperation.assert) := by
  induction expressions with
  | nil => trivial
  | cons head tail proof =>
      exact ⟨holds head List.mem_cons_self,
        proof (fun expression member => holds expression (List.mem_cons_of_mem _ member))⟩

theorem CleanExpression.of_combination_at [Field F] [DecidableEq F]
    (expression : Airbender.Expression F) (placement : Nat → Fin n)
    (relations : List (Polynomial n F)) (witness : Combination relations)
    (checked : equal (polynomial placement expression) (combination relations witness) = true)
    (address : Fin n → Address) (base : Address → F) (data : ProverData F)
    (holds : Satisfies relations (base ∘ address)) :
    expression.eval ⟨fun index => base (address (placement index)), data⟩ = 0 :=
  of_combination expression placement relations witness checked (base ∘ address) holds
    ⟨fun index => base (address (placement index)), data⟩ (fun _ _ => rfl)

/-- Append independently checked assertion batches. -/
theorem CleanExpression.append_assertions_hold [Field F]
    (first rest : List (Airbender.Expression F)) (environment : Environment F)
    (left : FlatOperation.ConstraintsHoldFlat environment (first.map FlatOperation.assert))
    (right : FlatOperation.ConstraintsHoldFlat environment (rest.map FlatOperation.assert)) :
    FlatOperation.ConstraintsHoldFlat environment ((first ++ rest).map FlatOperation.assert) := by
  induction first with
  | nil => exact right
  | cons head tail ih => exact ⟨left.1, ih left.2⟩

/-- Assemble Boolean checks for two explicit assertion batches. -/
theorem all_append_true (predicate : α → Bool) (first rest : List α)
    (left : first.all predicate = true) (right : rest.all predicate = true) :
    (first ++ rest).all predicate = true := by
  rw [List.all_append, left, right]
  rfl

end Airbender.Compiler
