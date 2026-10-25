import GKRCompiler.Arithmetic
import GKRProtocol.BorrowAssignment

namespace Airbender.Compiler
set_option warningAsError true
variable {F : Type}

def polynomialScopeCheck (bound : Nat) (polynomial : Polynomial n F) : Bool :=
  polynomial.all (fun term => term.2.all (fun wire => decide (wire.val < bound)))

theorem monomialValue_assignBorrows (monomial : Monomial n) (bound : Nat)
    (scope : ∀ wire ∈ monomial, wire.val < bound) (slots : Fin k → Fin n)
    (fresh : ∀ borrow, bound ≤ (slots borrow).val) (values : Fin n → Source.BaseField)
    (borrows : Fin k → Source.BaseField) :
    monomialValue (Source.assignBorrows slots values borrows) monomial = monomialValue values monomial := by
  have same (wire : Fin n) (member : wire ∈ monomial) :
      Source.assignBorrows slots values borrows wire = values wire := by
    apply Source.assignBorrows_frame
    intro borrow equalSlots
    have inside := scope wire member
    have outside := fresh borrow
    have equalValues := congrArg Fin.val equalSlots
    omega
  unfold monomialValue
  congr 1
  apply List.map_congr_left
  exact same

theorem evaluate_assignBorrows (polynomial : Polynomial n Source.BaseField) (bound : Nat)
    (scope : polynomialScopeCheck bound polynomial = true) (slots : Fin k → Fin n)
    (fresh : ∀ borrow, bound ≤ (slots borrow).val) (values : Fin n → Source.BaseField)
    (borrows : Fin k → Source.BaseField) :
    evaluate (Source.assignBorrows slots values borrows) polynomial = evaluate values polynomial := by
  unfold evaluate
  congr 1
  apply List.map_congr_left
  intro term member
  congr 1
  apply monomialValue_assignBorrows term.2 bound
  · intro wire included
    exact of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp scope term member) wire included)
  · exact fresh

def Expression.inputs : Expression n F → List (Fin n)
  | .constant _ => []
  | .atom wire => [wire]
  | .add left right | .mul left right => left.inputs ++ right.inputs

theorem Expression.value_congr [CommRing F] (expression : Expression n F) (left right : Fin n → F)
    (same : ∀ wire ∈ expression.inputs, left wire = right wire) : expression.value left = expression.value right := by
  induction expression with
  | constant _ => rfl
  | atom wire => exact same wire List.mem_cons_self
  | add first second firstProof secondProof =>
      exact congrArg₂ (· + ·)
        (firstProof (fun wire member => same wire (List.mem_append_left _ member)))
        (secondProof (fun wire member => same wire (List.mem_append_right _ member)))
  | mul first second firstProof secondProof =>
      exact congrArg₂ (· * ·)
        (firstProof (fun wire member => same wire (List.mem_append_left _ member)))
        (secondProof (fun wire member => same wire (List.mem_append_right _ member)))

def Expression.scopeCheck (bound : Nat) (expression : Expression n F) : Bool :=
  expression.inputs.all (fun wire => decide (wire.val < bound))

theorem Expression.assignBorrows_preserves (expression : Expression n Source.BaseField) (bound : Nat)
    (scope : expression.scopeCheck bound = true) (slots : Fin k → Fin n)
    (fresh : ∀ borrow, bound ≤ (slots borrow).val) (values : Fin n → Source.BaseField)
    (borrows : Fin k → Source.BaseField) :
    expression.value (Source.assignBorrows slots values borrows) = expression.value values := by
  apply expression.value_congr
  intro wire member
  apply Source.assignBorrows_frame
  intro borrow same
  have inside : wire.val < bound := of_decide_eq_true (List.all_eq_true.mp scope wire member)
  have outside := fresh borrow
  have equalValues := congrArg Fin.val same
  omega

theorem original_assertions_preserved (expressions : List (Expression n Source.BaseField)) (bound : Nat)
    (scope : expressions.all (Expression.scopeCheck bound) = true)
    (slots : Fin k → Fin n) (fresh : ∀ borrow, bound ≤ (slots borrow).val)
    (values : Fin n → Source.BaseField) (borrows : Fin k → Source.BaseField)
    (holds : Satisfies (expressions.map Expression.polynomial) values) :
    Satisfies (expressions.map Expression.polynomial) (Source.assignBorrows slots values borrows) := by
  intro polynomial member
  obtain ⟨expression, included, rfl⟩ := List.mem_map.mp member
  rw [Expression.polynomial_value,
    expression.assignBorrows_preserves bound (List.all_eq_true.mp scope expression included) slots fresh,
    ← Expression.polynomial_value]
  exact holds _ (List.mem_map.mpr ⟨expression, included, rfl⟩)

namespace Source

/-- Source execution advances the integer clock by four. This contract says
nothing about an emitted arithmetic constraint or its carry witness. -/
def clockContract (clock : Option (MemoryWord × MemoryWord)) (values : MemoryValues) : Prop :=
  match clock with
  | none => True
  | some (initial, final) =>
      (initial.timestamp values).Bounded ∧ (final.timestamp values).Bounded ∧
        (final.timestamp values).value = (initial.timestamp values).value + 4

def clockAssertionsFor : Option (MemoryWord × MemoryWord) → List HelperAssertion
  | none => []
  | some (initial, final) => clockAssertions initial final

theorem clock_assertions_complete (clock : Option (MemoryWord × MemoryWord)) (values : HelperValues)
    (contract : clockContract clock values.memory) :
    ∀ assertion ∈ clockAssertionsFor clock, assertion.value values = 0 := by
  cases clock with
  | none => intro assertion member; cases member
  | some pair =>
      exact clockAssertions_complete pair.1 pair.2 values contract.1 contract.2.1 contract.2.2

theorem borrow_assertions_complete (placement : HelperPlacement n) (slots : Fin k → Fin n)
    (unique : Function.Injective slots) (coordinates : ∀ borrow, slots borrow = placement.borrow borrow.val)
    (values : Fin n → BaseField) (borrows : Fin k → BaseField)
    (bits : ∀ borrow, borrows borrow * (borrows borrow - 1) = 0) :
    ∀ assertion ∈ borrowAssertions k,
      assertion.value (placement.project (assignBorrows slots values borrows)) = 0 := by
  intro assertion member
  obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp member
  have bounded : index < k := List.mem_range.mp inRange
  let borrow : Fin k := ⟨index, bounded⟩
  have same := assignBorrows_at slots unique values borrows borrow
  rw [coordinates borrow] at same
  change assignBorrows slots values borrows (placement.borrow index) *
    (assignBorrows slots values borrows (placement.borrow index) - 1) = 0
  rw [same]
  exact bits borrow

theorem canonical_borrow_assertions (placement : HelperPlacement n) (slots : Fin k → Fin n)
    (unique : Function.Injective slots) (coordinates : ∀ borrow, slots borrow = placement.borrow borrow.val)
    (values : Fin n → BaseField) (comparisons : List (MemoryWord × MemoryWord)) :
    let helpers := canonicalHelpers (placement.memory.project values) comparisons
    ∀ assertion ∈ borrowAssertions k, assertion.value
      (placement.project (assignBorrows slots values (fun borrow => helpers.borrow borrow.val))) = 0 := by
  apply borrow_assertions_complete placement slots unique coordinates values
  intro borrow
  exact canonicalHelpers_boolean (placement.memory.project values) comparisons borrow.val

end Source
end Airbender.Compiler
