import Airbender.Review.Circuits.ReducedMachine.BranchTheorems

namespace Tests.NativeReducedBranchRouting
open Airbender Arithmetic Trace ReducedMachine Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem exact_mask : branchMask = 70 ∧
    (List.range 18).map NativeBranchSelectorProofs.bit =
      [0,1,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

theorem update_flag_rejected {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) : w 17 ≠ 1 := by
  have flag : w 17 = 0 := by simpa [NativeBranchSelectorProofs.bit] using
    NativeBranchSelectorProofs.flags native mask ⟨0,by decide⟩
  simp [flag]

theorem ram_source_rejected {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) : w 88 ≠ 0 := by
  rw [(NativeBranchFieldProofs.source_port native mask).2.2]
  exact one_ne_zero

theorem dummy_write_rejected {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) : rdWrite w = #v[0,0] :=
  (branch_routing native mask).2.2.2.1

theorem zero_flag_rejected {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (nonzero : (w 61).val ≠ 0 ∨ (w 62).val ≠ 0) : w 68 ≠ 1 := by
  have zero := NativeBranchFieldProofs.equality_flag native mask
  have notBoth : ¬ ((w 61).val = 0 ∧ (w 62).val = 0) := by omega
  rw [if_neg notBoth] at zero
  simp [zero]

/-- These assignments check only the actual Boolean/zero-test assertion slice,
    not all117equations, lookups, original decoding or accepted execution. -/
private def zeroRow (nonzero : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 23 then 1 else if i = 61 ∨ i = 97 ∨ i = 99 then
    (if nonzero then 1 else 0) else if i = 68 then (if nonzero then 0 else 1) else 0

private def zeroIndices : Vector (Fin 117) 5 :=
  #v[⟨21,by decide⟩,⟨78,by decide⟩,⟨79,by decide⟩,⟨80,by decide⟩,⟨81,by decide⟩]

private def zeroAssertions (w : Nat → ZMod mersenne31Modulus) : Prop :=
  ∀ i : Fin 5, ((FlatOperation.constraints (importedConstraints NativeFixed.table)).get
    ⟨zeroIndices[i].val,by change zeroIndices[i].val < 117; exact zeroIndices[i].isLt⟩).eval
      (Verification.environment w) = 0

theorem actual_zero_slices (nonzero : Bool) : zeroAssertions (zeroRow nonzero) := by
  intro i
  cases nonzero <;> fin_cases i <;> decide +kernel

theorem independent_zero_values : zeroRow false 68 = 1 ∧ zeroRow true 68 = 0 ∧
    zeroRow true 61 = 1 ∧ zeroRow false 61 = 0 := by decide +kernel

end Tests.NativeReducedBranchRouting
