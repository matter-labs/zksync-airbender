import Airbender.Proofs.Trace.Families.JumpBranchSlt.Values
import Airbender.Proofs.JumpBranchSlt.Target

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Verification

/-- Initialized matching supplies indirect source ranges; original public
    decoding supplies PC/immediate ranges, JAL parity and exact jump selection. -/
theorem image_jump_targets {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val ∈ [1,2] →
      let w := row.assignment
      let base := Word.mk (w (if (w 12).val = 2 then 22 else 0)).val
        (w (if (w 12).val = 2 then 23 else 1)).val
      let sum := base.toBitVec + (Word.mk (w 9).val (w 10).val).toBitVec
      (Word.mk (w 13).val (w 14).val).toBitVec =
        (if (w 12).val = 2 then sum &&& 0xfffffffe else sum) ∧
      (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 := by
  have values := image_value_bounds image inputs accepted decoded
  intro row present jump
  obtain ⟨entry, _, source, query⟩ := decoded_sources (by decide) image accepted decoded row present
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at query member
  cases row with
  | mk family w =>
    cases family
    have fields := decoded_inputs (by decide) image native member
    let indirect : Bool := decide ((w 12).val = 2)
    have mask : (w 12).val = if indirect then 2 else 1 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at jump
      rcases jump with one | two
      · simp [indirect, one]
      · simp [indirect, two]
    obtain ⟨selected, other⟩ := jump_identity indirect native mask
    have sourceBound : (Word.mk (w 22).val (w 23).val).Bounded := by
      have bounded := values.1 ⟨.jumpBranchSlt,w⟩ present
        importedConstraintsMemoryPorts[0] (by
          change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
          simp [importedConstraintsMemoryPorts])
      rw [Trace.Proofs.read_word] at bounded
      exact bounded
    have baseBound : (Word.mk (w (if indirect then 22 else 0)).val
        (w (if indirect then 23 else 1)).val).Bounded := by
      cases chosen : indirect
      · exact fields.1
      · exact sourceBound
    have parity : indirect = false →
        (w (if indirect then 22 else 0)).val % 2 = 0 ∧ (w 9).val % 2 = 0 := by
      intro direct
      have one : (w 12).val = 1 := by simpa only [direct, Bool.false_eq_true, if_false] using mask
      have even := direct_offset_even source query one
      simp only [direct, Bool.false_eq_true, if_false]
      have aligned := fields.2.1
      change (w 0).val % 4 = 0 at aligned
      exact ⟨by omega, even⟩
    have target := jump_pc indirect native selected other
      (base := ⟨(w (if indirect then 22 else 0)).val, (w (if indirect then 23 else 1)).val⟩)
      (offset := ⟨(w 9).val, (w 10).val⟩)
      ⟨rfl,rfl,(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm⟩
      baseBound fields.2.2.1 parity
    simpa [indirect] using target

end Airbender.JumpBranchSlt.Proofs
