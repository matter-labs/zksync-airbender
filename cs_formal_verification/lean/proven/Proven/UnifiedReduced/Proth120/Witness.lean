module
public import Human.Circuits.UnifiedReduced.Proth120Modular
public import Human.Circuits.UnifiedReduced.Tables.Proth120
public import Proven.UnifiedReduced.Modular.Witness
public import Proven.WitnessCheck
public import Proven.KernelRfl
public import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.Witness
open Verification

abbrev assignment := @Modular.Witness.assignment proth120Modulus

abbrev setup := tableWith (fun _ => 0)

noncomputable def checked (words : Nat → BitVec 32) : CheckedTable (ZMod proth120Modulus) :=
  rowsChecked (tableWith words).toRaw [Vector.replicate 10 0] (by
    intro row h
    obtain rfl := List.mem_singleton.mp h
    exact ⟨⟨0, by decide⟩, by kernel_rfl⟩)

theorem holds (op : AddSub.Modular.Opcode) (words : Nat → BitVec 32 := fun _ => 0) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment op)) (importedConstraints (tableWith words)) := by
  apply holds_of_checkOps (tables := List.replicate 15 range16Checked ++ List.replicate 5 (checked words))
  · rfl
  · cases op <;> kernel_rfl

theorem clocks (op : AddSub.Modular.Opcode) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment op))
      (importedConstraintsTimestampLookups (p := proth120Modulus)) := by
  apply holds_of_checkOps (tables := List.replicate 8 timestampChecked)
  · rfl
  · cases op <;> kernel_rfl

theorem selected (op : AddSub.Modular.Opcode) (k : Nat) (lo : 11 ≤ k) (hi : k ≤ 20) :
    assignment op k = if k = op.selector + 1 then 1 else 0 := by
  interval_cases k <;> cases op <;> rfl

end Airbender.UnifiedReduced.Proth120.Witness
