import Airbender.Proofs.Trace.Families.JumpBranchSlt.Values
import Airbender.Proofs.JumpBranchSlt.Branch

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Verification

/-- Original public branch metadata retains exactly the six architectural tags. -/
theorem branch_field_tag {instruction : SailRV32.instruction} {data : DecoderData Unit}
    (fields : decoderFields instruction = some data) (mask : data.mask = 16) :
    data.funct3 ∈ [0,1,4,5,6,7] := by
  unfold decoderFields at fields
  split at fields
  all_goals
    first
    | solve | cases fields
    | rw [← Option.some.inj fields] at mask ⊢
      first
      | solve | simp_all
      | cases ‹SailRV32.bop› <;> simp [Branch.funct3]

/-- Complete initialized matching supplies both operand ranges; original public
    decoding fixes branch identity/tags before native condition resolution. -/
theorem image_branches {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val = 16 →
      let w := row.assignment
      let taken := branchCondition (w 11).val (Word.mk (w 22).val (w 23).val)
        (Word.mk (w 24).val (w 25).val)
      (w 46).val = (if taken then 1 else 0) ∧
      (w 45).val = (if taken then 0 else 1) ∧
      (Word.mk (w 38).val (w 39).val).value = 0 := by
  have values := image_value_bounds image inputs accepted decoded
  intro row present mask
  obtain ⟨entry,_,source,query⟩ := decoded_sources (by decide) image accepted decoded row present
  have native := accepted.constraints row present
  rw [row_decoder_query] at query
  have fieldBounds := decoder_field_bounds source.fields
  have small : entry.data.mask < mersenne31Modulus := by
    have cases := fieldBounds.2.1
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at cases
    rcases cases with eq | eq | eq | eq | eq <;> rw [eq] <;> decide
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change row.assignment 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  have entryMask : entry.data.mask = 16 := by
    rwa [packed,ZMod.val_natCast_of_lt small] at mask
  have tags : (row.assignment 11).val ∈ [0,1,4,5,6,7] := by
    rw [query_tag (by decide) source.fields query]
    exact branch_field_tag source.fields entryMask
  cases row with
  | mk family w =>
    cases family
    change FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints at native
    change (w 12).val = 16 at mask
    change (w 11).val ∈ [0,1,4,5,6,7] at tags
    obtain ⟨selected,other⟩ := branch_selectors (w := w) (by decide) native mask
    have reads (i : Fin 2) :
        (readToken w importedConstraintsMemoryPorts[i.val]).word.Bounded :=
      values.1 ⟨.jumpBranchSlt,w⟩ present _ (by
        change importedConstraintsMemoryPorts[i.val] ∈ importedConstraintsMemoryPorts
        fin_cases i <;> simp [importedConstraintsMemoryPorts])
    have leftBound : (Word.mk (w 22).val (w 23).val).Bounded := by
      have range := reads ⟨0,by decide⟩
      rw [Trace.Proofs.read_word] at range
      exact range
    have rightBound : (Word.mk (w 24).val (w 25).val).Bounded := by
      have range := reads ⟨1,by decide⟩
      rw [Trace.Proofs.read_word] at range
      exact range
    have resolved := branch_resolution native selected other tags
      (left := ⟨(w 22).val,(w 23).val⟩) (right := ⟨(w 24).val,(w 25).val⟩)
      ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm⟩ leftBound rightBound
    exact branch_effects _ native selected other resolved

end Airbender.JumpBranchSlt.Proofs
