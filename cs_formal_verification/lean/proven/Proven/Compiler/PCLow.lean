module
public import Human.Helpers.Decoder.PooledProgram
public import Proven.AddSub.PC
public import Proven.JumpBranchSlt
public import Proven.MulDiv
public import Proven.ShiftBinop
public import Proven.WordMemory
public import Proven.SubwordMemory
public import Proven.UnifiedReduced
public import Human.Helpers.UnifiedReduced.Registry

@[expose] public section
namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic

theorem final_pc_low_bound {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w Variables.finalPCLo).val < limbBase := by
  have low := (local_ranges h).2.2.2
  have cleanup := (lookup_values hp h).2.2.2.2
  rw [cleanup, ZMod.val_natCast_of_lt (by
    dsimp [limbBase] at low
    omega : (w 36).val - (w 36).val % 4 < p)]
  exact lt_of_le_of_lt (Nat.sub_le _ _) low


end Airbender.JumpBranchSlt.Proofs

namespace Airbender.Trace.NativeDecoder.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false

/-- The guarded decoder limb is independently ranged on every native outgoing
    PC. This uses the low limb only and preserves the noncanonical high-PC case. -/
theorem pooled_final_pc_low [Fact p.Prime] (hp : 4194304 ≤ p)
    (row : Row p PooledFamily) (setup : PooledSetup p)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup)) : row.finish.word.lo < limbBase := by
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      have actual := AddSub.Proofs.pc_bounds core
        (initial := ⟨(w 0).val, (w 1).val⟩) (final := ⟨(w 19).val, (w 20).val⟩)
        ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
      exact actual.1
    | wordMemory =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (WordMemory.importedConstraints setup.wordMemory)
          WordMemory.importedConstraintsTimestampLookups)
      exact (WordMemory.Proofs.local_ranges core).2.1
    | jumpBranchSlt =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
      exact JumpBranchSlt.Proofs.final_pc_low_bound hp core
    | mulDiv =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left MulDiv.importedConstraints MulDiv.importedConstraintsTimestampLookups)
      exact MulDiv.Proofs.local_ranges core ⟨6, by decide⟩
    | shiftBinop =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left ShiftBinop.importedConstraints ShiftBinop.importedConstraintsTimestampLookups)
      exact (ShiftBinop.Proofs.local_ranges core).1
    | subwordMemory =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (SubwordMemory.importedConstraints setup.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      exact (SubwordMemory.Proofs.local_ranges core).2.2.2.1


end Airbender.Trace.NativeDecoder.Proofs
