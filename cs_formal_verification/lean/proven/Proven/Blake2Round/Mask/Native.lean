module
public import Proven.Blake2Round.Mask.Row

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic

/-- Interpret only actual native source words and Boolean control columns. -/
def inputOf (w : Nat → ZMod babyBearModulus) : Input :=
  ⟨readWord w 42, fun round => decide (w (142 + round.val) = 1),
    decide (w 139 = 1), decide (w 141 = 1), decide (w 140 = 1), readWord w 0, readWord w 25,
    Vector.ofFn fun i => readWord w ⟨1 + i.val, by have := i.isLt; omega⟩,
    Vector.ofFn fun i => readWord w ⟨9 + i.val, by have := i.isLt; omega⟩,
    Vector.ofFn fun i => readWord w ⟨26 + i.val, by have := i.isLt; omega⟩⟩

/-- Observe native destination words and addresses. -/
def outputOf (w : Nat → ZMod babyBearModulus) : Output :=
  ⟨writtenWord w 42, Vector.ofFn fun i => writtenWord w ⟨1 + i.val, by have := i.isLt; omega⟩,
    Vector.ofFn fun i => writtenWord w ⟨9 + i.val, by have := i.isLt; omega⟩,
    importedConstraintsIndirectPorts.map fun port => port.address w⟩

/-- A checked Boolean field value equals its Boolean interpretation. -/
theorem boolean_value {value : ZMod babyBearModulus} (bit : value = 0 ∨ value = 1) :
    value = if decide (value = 1) then 1 else 0 := by
  rcases bit with rfl | rfl <;> simp

/-- Imported control-bit constraints establish the observable native mapping. -/
theorem native_mapping {w : Nat → ZMod babyBearModulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    Mapping (inputOf w) (outputOf w) w := by
  have controls := Control.Proofs.control_bits constraints
  refine {
    controller := rfl
    controllerOutput := rfl
    statePointer := rfl
    messagePointer := rfl
    rounds := ?_
    reduced := ?_
    compression := ?_
    inputIsRight := ?_
    state := rfl
    extended := rfl
    message := rfl
    stateOutput := rfl
    extendedOutput := rfl
    addresses := rfl
  }
  · intro round
    have indices : ∀ round : Fin 10,
        Variables.controlBits[(⟨3 + round.val, by have := round.isLt; omega⟩ : Fin 13)] = 142 + round.val := by decide
    have bit := controls ⟨3 + round.val, by have := round.isLt; omega⟩
    rw [indices] at bit
    exact boolean_value bit
  · exact boolean_value (controls 0)
  · exact boolean_value (controls 2)
  · exact boolean_value (controls 1)

/-- Initialized native read bounds supply every source-word assumption. -/
theorem native_assumptions {w : Nat → ZMod babyBearModulus}
    (reads : ∀ i : Fin 43, (readWord w i).Bounded) : Assumptions (inputOf w) where
  controller := reads 42
  pointers := ⟨reads 0, reads 25⟩
  state i := by simpa only [inputOf, Fin.getElem_fin, Vector.getElem_ofFn] using reads ⟨1 + i.val, by have := i.isLt; omega⟩
  extended i := by simpa only [inputOf, Fin.getElem_fin, Vector.getElem_ofFn] using reads ⟨9 + i.val, by have := i.isLt; omega⟩
  message i := by simpa only [inputOf, Fin.getElem_fin, Vector.getElem_ofFn] using reads ⟨26 + i.val, by have := i.isLt; omega⟩

/-- Every initialized accepted native row follows the full Boolean-mask reference. -/
theorem native_effect {w : Nat → ZMod babyBearModulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (reads : ∀ i : Fin 43, (readWord w i).Bounded) : spec (inputOf w) (outputOf w) :=
  soundness _ _ w (native_assumptions reads) constraints (native_mapping constraints)

end Airbender.Blake2Round.Mask.Proofs
