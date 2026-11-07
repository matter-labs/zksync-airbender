import Airbender.Proofs.GKRProtocol.HelperValidity
import Airbender.Proofs.GKRProtocol.InactiveHistory
import Airbender.Proofs.GKRProtocol.BaseAssignment

namespace Airbender.Compiler
set_option warningAsError true

theorem evaluate_congr_on (polynomial : Polynomial n Source.BaseField)
    (left right : Fin n → Source.BaseField)
    (same : ∀ term ∈ polynomial, ∀ wire ∈ term.2, left wire = right wire) :
    evaluate left polynomial = evaluate right polynomial := by
  unfold evaluate
  congr 1
  apply List.map_congr_left
  intro term member
  congr 1
  unfold monomialValue
  congr 1
  apply List.map_congr_left
  exact same term member

def Source.HelperField.transportCheck (field : Source.HelperField)
    (sourcePlacement : Source.HelperPlacement n) (nativePlacement : Source.HelperPlacement m)
    (inputBank : WireBank n) (nativeBank : WireBank m) : Bool :=
  let polynomial := field.polynomial nativePlacement
  polynomial.all (fun term => term.2.all (fun wire =>
    decide (inputBank.address (inputBank.placement (nativeBank.address wire)) = nativeBank.address wire))) &&
    decide (rename (inputBank.placement ∘ nativeBank.address) polynomial = field.polynomial sourcePlacement)

theorem Source.HelperField.transport_value (field : Source.HelperField)
    (sourcePlacement : Source.HelperPlacement n) (nativePlacement : Source.HelperPlacement m)
    (inputBank : WireBank n) (nativeBank : WireBank m)
    (checked : field.transportCheck sourcePlacement nativePlacement inputBank nativeBank = true)
    (source : Fin n → Source.BaseField) (base : GKRAddress → Source.BaseField)
    (inputs : ∀ wire, base (inputBank.address wire) = source wire) :
    field.value (nativePlacement.project (base ∘ nativeBank.address)) =
      field.value (sourcePlacement.project source) := by
  have parts : (field.polynomial nativePlacement).all (fun term => term.2.all (fun wire =>
      decide (inputBank.address (inputBank.placement (nativeBank.address wire)) = nativeBank.address wire))) = true ∧
      rename (inputBank.placement ∘ nativeBank.address) (field.polynomial nativePlacement) =
        field.polynomial sourcePlacement := by
    simpa only [transportCheck, Bool.and_eq_true, decide_eq_true_eq] using checked
  rw [← field.polynomial_value, ← field.polynomial_value, ← parts.2, evaluate_rename]
  apply evaluate_congr_on
  intro term member wire included
  have roundTrip : inputBank.address (inputBank.placement (nativeBank.address wire)) = nativeBank.address wire :=
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp parts.1 term member) wire included)
  exact (congrArg base roundTrip).symm.trans (inputs _)

theorem evaluate_assignBorrows_disjoint (polynomial : Polynomial n Source.BaseField)
    (slots : Fin k → Fin n) (values : Fin n → Source.BaseField) (borrows : Fin k → Source.BaseField)
    (checked : erasureUntouched (List.ofFn slots) polynomial = true) :
    evaluate (Source.assignBorrows slots values borrows) polynomial = evaluate values polynomial := by
  unfold evaluate
  congr 1
  apply List.map_congr_left
  intro term member
  congr 1
  unfold monomialValue
  congr 1
  apply List.map_congr_left
  intro wire included
  apply Source.assignBorrows_frame
  intro borrow same
  have outside : wire ∉ List.ofFn slots := by
    have clause := List.all_eq_true.mp (List.all_eq_true.mp checked term member) wire included
    simpa using clause
  exact outside (List.mem_ofFn.mpr ⟨borrow, same⟩)

namespace Source

def HelperField.borrowCheck (placement : HelperPlacement n) (slots : Fin k → Fin n) : HelperField → Bool
  | .memory field => erasureUntouched (List.ofFn slots) (field.polynomial placement.memory)
  | .borrow index => decide (index < k)
  | .add left right => left.borrowCheck placement slots && right.borrowCheck placement slots
  | .scale _ inner | .neg inner => inner.borrowCheck placement slots

theorem HelperField.assignBorrows_value (field : HelperField) (placement : HelperPlacement n)
    (slots : Fin k → Fin n) (unique : Function.Injective slots)
    (coordinates : ∀ borrow, slots borrow = placement.borrow borrow.val)
    (checked : field.borrowCheck placement slots = true)
    (values : Fin n → BaseField) (borrows : Fin k → BaseField) :
    field.value (placement.project (assignBorrows slots values borrows)) =
      field.value ⟨placement.memory.project values, fun index =>
        if bounded : index < k then borrows ⟨index, bounded⟩ else 0⟩ := by
  induction field with
  | memory field =>
      change field.value (placement.memory.project (assignBorrows slots values borrows)) =
        field.value (placement.memory.project values)
      rw [← MemoryField.polynomial_value, ← MemoryField.polynomial_value]
      exact evaluate_assignBorrows_disjoint _ slots values borrows checked
  | borrow index =>
      have bounded : index < k := of_decide_eq_true checked
      have assigned := assignBorrows_at slots unique values borrows ⟨index, bounded⟩
      rw [coordinates ⟨index, bounded⟩] at assigned
      simpa only [HelperField.value, HelperPlacement.project, Function.comp_apply, dif_pos bounded] using assigned
  | add left right leftProof rightProof =>
      have parts : left.borrowCheck placement slots = true ∧ right.borrowCheck placement slots = true := by
        simpa only [borrowCheck, Bool.and_eq_true] using checked
      exact congrArg₂ (· + ·) (leftProof parts.1) (rightProof parts.2)
  | scale coefficient inner proof => exact congrArg ((coefficient : BaseField) * ·) (proof checked)
  | neg inner proof => exact congrArg Neg.neg (proof checked)

theorem HelperField.value_borrow_congr (field : HelperField) (memory : MemoryValues)
    (first second : Nat → BaseField) (bound : Nat) (placement : HelperPlacement n) (slots : Fin bound → Fin n)
    (checked : field.borrowCheck placement slots = true)
    (same : ∀ index, index < bound → first index = second index) :
    field.value ⟨memory, first⟩ = field.value ⟨memory, second⟩ := by
  induction field with
  | memory _ => rfl
  | borrow index => exact same index (of_decide_eq_true checked)
  | add left right leftProof rightProof =>
      have parts : left.borrowCheck placement slots = true ∧ right.borrowCheck placement slots = true := by
        simpa only [borrowCheck, Bool.and_eq_true] using checked
      exact congrArg₂ (· + ·) (leftProof parts.1) (rightProof parts.2)
  | scale coefficient inner proof => exact congrArg ((coefficient : BaseField) * ·) (proof checked)
  | neg inner proof => exact congrArg Neg.neg (proof checked)

theorem HelperField.assignCanonical_value (field : HelperField) (placement : HelperPlacement n)
    (slots : Fin k → Fin n) (unique : Function.Injective slots)
    (coordinates : ∀ borrow, slots borrow = placement.borrow borrow.val)
    (checked : field.borrowCheck placement slots = true) (values : Fin n → BaseField)
    (comparisons : List (MemoryWord × MemoryWord)) :
    let helpers := canonicalHelpers (placement.memory.project values) comparisons
    field.value (placement.project (assignBorrows slots values (fun index => helpers.borrow index.val))) =
      field.value helpers := by
  dsimp only
  rw [field.assignBorrows_value placement slots unique coordinates checked]
  apply field.value_borrow_congr _ _ _ k placement slots checked
  intro index bounded
  simp only [dif_pos bounded]
  rfl

end Source
end Airbender.Compiler
