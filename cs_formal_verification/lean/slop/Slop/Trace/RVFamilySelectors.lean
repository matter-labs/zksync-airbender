import Slop.Trace.RVProgram
import Slop.AddSub.Selectors
import Slop.WordMemory

/-! ADD/SUB and LW/SW row selectors from the RV program entry (the restricted-scope families of `RVZeroPooled`). -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- The selectors of an ADD/SUB or LW/SW row are the bits of its entry's mask (as `row_query_selectors_of_bound`). -/
theorem rv_row_query_selectors_of_bound {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {row : Row p} (setup : Table (ZMod p) (fields 9))
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup))
    {entry : RVProgramEntry} (small : entry.data.mask < 512)
    (equal : row.decoderQuery = entry.query) :
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 := by
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) equal
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      have flags := (AddSub.Proofs.local_flags core).2
      have boolean : ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 0 ∨
          w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 1 := by
        intro i
        have bit := flags i
        fin_cases i <;> simpa using bit
      change (∑ i : Fin 9, (2 ^ i.val : Nat) * w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) =
        (entry.data.mask : ZMod p) at packed
      exact unpack_decoder_bits (by dsimp [limbBase] at hp; omega) small boolean packed
    | wordMemory =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (WordMemory.importedConstraints setup)
          WordMemory.importedConstraintsTimestampLookups)
      have boolean : w 10 = 0 ∨ w 10 = 1 := WordMemory.Proofs.local_flags core 1
      change (∑ i : Fin 1, (2 ^ i.val : Nat) * w #[10][i]) = (entry.data.mask : ZMod p) at packed
      have scalar : w 10 = (entry.data.mask : ZMod p) := by simpa using packed
      have value := congrArg ZMod.val scalar
      rw [ZMod.val_natCast_of_lt (by dsimp [limbBase] at hp; omega : entry.data.mask < p)] at value
      change ∀ i : Fin 1, w #[10][i] = if entry.data.mask.testBit i.val then 1 else 0
      intro i
      have index : i = 0 := Fin.eq_zero i
      subst i
      rcases boolean with zero | one
      · simp only [zero, ZMod.val_zero] at value
        rw [← value]
        exact zero
      · have oneval : (1 : ZMod p).val = 1 := by
          simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (by dsimp [limbBase] at hp; omega : 1 < p))
        simp only [one, oneval] at value
        rw [← value]
        exact one

end Airbender.Trace.Proofs
