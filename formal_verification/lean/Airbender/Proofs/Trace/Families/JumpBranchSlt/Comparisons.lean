import Airbender.Proofs.Trace.Families.JumpBranchSlt.Values
import Airbender.Proofs.JumpBranchSlt.Comparison

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Verification

/-- Native comparison metadata has the original signed/unsigned funct3 values. -/
theorem comparison_field_tag {instruction : SailRV32.instruction} {data : DecoderData Unit}
    (fields : decoderFields instruction = some data) (mask : data.mask ∈ [4,8]) :
    data.funct3 ∈ [2,3] := by
  unfold decoderFields at fields
  split at fields
  all_goals first | (solve | cases fields) | (rw [← Option.some.inj fields] at mask ⊢; simp_all)

/-- Public byte construction and complete native matching derive the operand
    ranges, immediate choice, signedness and x0 mask used by the numerical proof. -/
theorem image_comparisons {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val ∈ [4,8] →
      let w := row.assignment
      let left := Word.mk (w 22).val (w 23).val
      let right := Word.mk (w (if (w 12).val = 8 then 9 else 24)).val
        (w (if (w 12).val = 8 then 10 else 25)).val
      (Word.mk (w 38).val (w 39).val).value =
        if (w 7).val = 0 then 0 else
        if (w 11).val = 2 then (if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0)
        else (if left.value < right.value then 1 else 0) := by
  have values := image_value_bounds image inputs accepted decoded
  intro row present mask
  obtain ⟨entry,_,source,query⟩ := decoded_sources (by decide) image accepted decoded row present
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at query member
  have fieldBounds := decoder_field_bounds source.fields
  have small : entry.data.mask < mersenne31Modulus := by
    have cases := fieldBounds.2.1
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at cases
    rcases cases with eq | eq | eq | eq | eq <;> rw [eq] <;> decide
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change row.assignment 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  have entryMask : entry.data.mask ∈ [4,8] := by
    rwa [packed,ZMod.val_natCast_of_lt small] at mask
  have tagValues : (row.assignment 11).val ∈ [2,3] := by
    rw [query_tag (by decide) source.fields query]
    exact comparison_field_tag source.fields entryMask
  cases row with
  | mk family w =>
    cases family
    change FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints at native
    change setup.table.Contains #[] (decoderQuery w) at member
    change decoderQuery w = entry.query at query
    change (w 12).val ∈ [4,8] at mask
    change (w 11).val ∈ [2,3] at tagValues
    have fields := decoded_inputs (w := w) (by decide) image native member
    let immediate : Bool := decide ((w 12).val = 8)
    let signed : Bool := decide ((w 11).val = 2)
    have maskEq : (w 12).val = if immediate then 8 else 4 := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at mask
      rcases mask with four | eight
      · simp [immediate,four]
      · simp [immediate,eight]
    have tagEq : w 11 = if signed then 2 else 3 := by
      have eq : (w 11).val = if signed then 2 else 3 := by
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at tagValues
        rcases tagValues with two | three
        · simp [signed,two]
        · simp [signed,three]
      have cast := congrArg (fun n : Nat => (n : ZMod mersenne31Modulus)) eq
      cases chosen : signed <;> simpa only [chosen,Bool.false_eq_true,if_false,if_true,
        Nat.cast_ofNat,ZMod.natCast_zmod_val] using cast
    obtain ⟨selected,other⟩ := comparison_selectors (w := w) (by decide) immediate native maskEq
    have reads (i : Fin 2) :
        (readToken w importedConstraintsMemoryPorts[i.val]).word.Bounded :=
      values.1 ⟨.jumpBranchSlt,w⟩ present _ (by
        change importedConstraintsMemoryPorts[i.val] ∈ importedConstraintsMemoryPorts
        fin_cases i <;> simp [importedConstraintsMemoryPorts])
    have leftBound : (Word.mk (w 22).val (w 23).val).Bounded := by
      have range := reads ⟨0,by decide⟩
      rw [Trace.Proofs.read_word] at range
      exact range
    have rightBound : (Word.mk (w (if immediate then 9 else 24)).val
        (w (if immediate then 10 else 25)).val).Bounded := by
      cases chosen : immediate
      · have range := reads ⟨1,by decide⟩
        rw [Trace.Proofs.read_word] at range
        exact range
      · exact fields.2.2.1
    have resolved := comparison_resolution immediate signed native selected other tagEq
      (left := ⟨(w 22).val,(w 23).val⟩)
      (right := ⟨(w (if immediate then 9 else 24)).val,(w (if immediate then 10 else 25)).val⟩)
      ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm⟩ leftBound rightBound
    let answer : Nat := if signed then
      (if (Word.mk (w 22).val (w 23).val).toBitVec.toInt <
        (Word.mk (w (if immediate then 9 else 24)).val (w (if immediate then 10 else 25)).val).toBitVec.toInt then 1 else 0)
      else (if (Word.mk (w 22).val (w 23).val).value <
        (Word.mk (w (if immediate then 9 else 24)).val (w (if immediate then 10 else 25)).val).value then 1 else 0)
    have answerBound : answer < mersenne31Modulus := by dsimp [answer]; split_ifs <;> decide
    have resolvedValue : (w 35).val = answer := by
      rw [resolved]
      exact ZMod.val_natCast_of_lt answerBound
    have flagEq : w 8 = if (w 7).val = 0 then 1 else 0 := fields.2.2.2
    have flag : w 8 = 0 ∨ w 8 = 1 := by
      rw [flagEq]
      split_ifs <;> simp
    have total : w 19 + w 20 = 1 := by
      cases chosen : immediate <;> simp only [chosen,Bool.false_eq_true,if_false,if_true] at selected
      all_goals simp only [selected.1,selected.2,zero_add,add_zero]
    have result := comparison_destination native total ⟨other.1,other.2.1⟩ flag
    rw [flagEq,resolvedValue] at result
    by_cases zero : (w 7).val = 0
    · simpa [zero] using result
    · simpa [zero,answer,immediate,signed] using result

end Airbender.JumpBranchSlt.Proofs
