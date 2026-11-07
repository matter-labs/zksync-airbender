import Airbender.Review.Circuits.ReducedMachine.JumpTheorems

namespace Tests.NativeReducedJump
open Airbender Arithmetic Trace ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- These actual reduced masks differ from old split control-family masks. -/
theorem exact_masks : jumpMask false = 257 ∧ jumpMask true = 33025 ∧
    (List.finRange 18).map (fun i => NativeJumpSelectorProofs.bit false i.val) =
      [1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0] ∧
    (List.finRange 18).map (fun i => NativeJumpSelectorProofs.bit true i.val) =
      [1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0] := by decide +kernel

theorem ram_source_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) : w 88 ≠ 0 := by
  rw [(NativeJumpFieldProofs.source_port native jal mask).2.2]
  exact one_ne_zero

/-- The readonly second source remains rs2 even though the selected word is immediate. -/
theorem immediate_readonly {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    source2 w = #v[w 9,w 10] ∧ w 39 = w 6 ∧ w 40 = 0 :=
  ⟨NativeJumpFieldProofs.source native jal mask,(NativeJumpFieldProofs.source_port native jal mask).1,
    (NativeJumpFieldProofs.source_port native jal mask).2.1⟩

/-- A field-level discarded write does not discard the actual return candidate.
    Original public rd/x0 binding is a later obligation. -/
theorem discarded_return {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) (zero : rdZeroFlag w = 1) :
    jumpCandidate w = defaultPC w ∧ rdWrite w = #v[0,0] := by
  refine ⟨NativeJumpFieldProofs.candidate native jal mask,?_⟩
  rw [(NativeJumpFieldProofs.write native jal mask).2]
  simp [zero,jumpCandidate]

theorem raw_misalignment_rejected {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    (w 61).val / 2 % 2 ≠ 1 := by
  rw [NativeJumpNumericalProofs.raw_bit1 native jal mask]
  decide

/-- Actual cleanup/selection rejects oversized final limbs without any local
    source/target range, original decoded result or expected PC premise. -/
theorem oversized_final_rejected {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    (w 13).val < 65536 ∧ (w 14).val < 65536 :=
  (jump_pc_bounds native jal mask).1

-- Six actual assertions only, not full117-equation/lookups/accepted/Sail execution.
private def row (jal : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 16 else if i = 9 then 4 else if i = 17 ∨ i = 25 then 1 else
  if i = 32 then (if jal then 1 else 0) else if i = 35 then 48 else
  if i = 81 then (if jal then 16 else 48) else if i = 61 then (if jal then 20 else 52) else 0
private def indices : Vector (Fin 117) 6 :=
  #v[⟨20,by decide⟩,⟨23,by decide⟩,⟨46,by decide⟩,⟨47,by decide⟩,⟨74,by decide⟩,⟨75,by decide⟩]
private def assertions (w : Nat → ZMod mersenne31Modulus) : Prop :=
  ∀ i : Fin 6, ((FlatOperation.constraints (importedConstraints NativeFixed.table)).get
    ⟨indices[i].val,by change indices[i].val < 117; exact indices[i].isLt⟩).eval (environment w) = 0

theorem actual_base_add_slices (jal : Bool) : assertions (row jal) := by
  intro i
  cases jal <;> fin_cases i <;> decide +kernel

theorem independent_slice_values :
    (jumpBaseWord (row true)).toBitVec = 16 ∧ (jumpRawTargetWord (row true)).toBitVec = 20 ∧
    (jumpBaseWord (row false)).toBitVec = 48 ∧ (jumpRawTargetWord (row false)).toBitVec = 52 := by decide +kernel

end Tests.NativeReducedJump
