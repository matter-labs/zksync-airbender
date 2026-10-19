import Airbender.Proofs.Trace.Families.JumpBranchSlt.Decoder
import Airbender.Proofs.JumpBranchSlt.ComparisonPC

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Verification

/-- Public original decoding supplies incoming PC ranges/alignment; native
    packed masks recover comparison selection. No source-register read is needed. -/
theorem image_comparison_pc {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val ∈ [4,8] →
      let w := row.assignment
      (Word.mk (w 13).val (w 14).val).toBitVec =
        (Word.mk (w 0).val (w 1).val).toBitVec + 4 ∧
      (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 := by
  intro row present mask
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at member
  cases row with
  | mk family w =>
    cases family
    change FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints at native
    change setup.table.Contains #[] (decoderQuery w) at member
    change (w 12).val ∈ [4,8] at mask
    have fields := decoded_inputs (w := w) (by decide) image native member
    let immediate : Bool := decide ((w 12).val = 8)
    have maskEq : (w 12).val = if immediate then 8 else 4 := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at mask
      rcases mask with four | eight
      · simp [immediate,four]
      · simp [immediate,eight]
    obtain ⟨selected,other⟩ := comparison_selectors (w := w) (by decide) immediate native maskEq
    have pair : w 19 + w 20 = 1 := by
      rw [selected.1,selected.2]
      cases immediate <;> simp
    exact comparison_pc native pair other fields.1 fields.2.1

end Airbender.JumpBranchSlt.Proofs
