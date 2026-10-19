import Airbender.Proofs.Trace.Families.JumpBranchSlt.Branches
import Airbender.Proofs.JumpBranchSlt.BranchPC

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Verification

/-- The checked initialized branch condition selects the native target.
    Original public decoding supplies PC/offset bounds, alignment and parity;
    both output bounds and all carries come from actual native queries. -/
theorem image_branch_targets {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val = 16 →
      let w := row.assignment
      let pc := (Word.mk (w 0).val (w 1).val).toBitVec
      let offset := (Word.mk (w 9).val (w 10).val).toBitVec
      let taken := branchCondition (w 11).val (Word.mk (w 22).val (w 23).val)
        (Word.mk (w 24).val (w 25).val)
      (Word.mk (w 13).val (w 14).val).toBitVec = (if taken then pc+offset else pc+4) ∧
      (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 := by
  have branches := image_branches image inputs accepted decoded
  intro row present mask
  have effects := branches row present mask
  obtain ⟨entry,_,source,query⟩ := decoded_sources (by decide) image accepted decoded row present
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at query member
  cases row with
  | mk family w =>
    cases family
    change FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints at native
    change setup.table.Contains #[] (decoderQuery w) at member
    change decoderQuery w = entry.query at query
    change (w 12).val = 16 at mask
    have fields := decoded_inputs (w := w) (by decide) image native member
    have parity := branch_offset_even source query mask
    obtain ⟨selected,other⟩ := branch_selectors (w := w) (by decide) native mask
    let taken := branchCondition (w 11).val (Word.mk (w 22).val (w 23).val)
      (Word.mk (w 24).val (w 25).val)
    have bit : (w 46).val = if taken then 1 else 0 := effects.1
    have resolved : w 46 = if taken then 1 else 0 := by
      have cast := congrArg (fun n : Nat => (n : ZMod mersenne31Modulus)) bit
      cases chosen : taken <;> simpa only [chosen,Bool.false_eq_true,if_false,if_true,
        Nat.cast_one,Nat.cast_zero,ZMod.natCast_zmod_val] using cast
    exact branch_pc taken native selected other resolved
      (initial := ⟨(w 0).val,(w 1).val⟩) (offset := ⟨(w 9).val,(w 10).val⟩)
      ⟨rfl,rfl,(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm⟩
      fields.1 fields.2.1 fields.2.2.1 parity

end Airbender.JumpBranchSlt.Proofs
