import Airbender.Proofs.ShiftBinop.BinaryResults
import Airbender.Proofs.ShiftBinop.ShiftSourceBounds
import Airbender.Proofs.ShiftBinop.SllLimbResult
import Airbender.Proofs.ShiftBinop.SrlLimbResult
import Airbender.Proofs.ShiftBinop.SraLimbResult

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native low-limb truncation is the architectural low-five-bit amount, even
    before bounding the rest of the selected register/immediate operand. -/
theorem word_shift_amount (word : Word) :
    (word.toBitVec.extractLsb' 0 5).toNat = word.lo % 32 := by
  norm_num [Word.toBitVec,Word.value,limbBase,BitVec.extractLsb',
    BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega

/-- Canonical source keys connect the actual native contributions to a whole
    RV32 shift. The caller derives the source range from initialized history. -/
theorem shift_selected_result {w : Nat → ZMod mersenne31Modulus} {kind : ShiftKind}
    (contributions : ShiftContributions w kind) (source : (left w).Bounded) :
    (selectedWord w).toBitVec = kind.result (left w).toBitVec
      ((right w).toBitVec.extractLsb' 0 5).toNat := by
  have amount : (w 29).val < 32 := by
    rw [contributions.amount]
    exact Nat.mod_lt _ (by decide)
  have parts := shift_part_words contributions source
  rw [word_shift_amount]
  change _ = kind.result (left w).toBitVec ((w 27).val % 32)
  rw [← contributions.amount,contributions.selected,parts 0,parts 1,parts 2]
  simp only [Word.ofBitVec_roundtrip]
  cases kind
  · exact sll_limb_result _ _ ⟨_,amount⟩ source.1 source.2
  · exact srl_limb_result _ _ ⟨_,amount⟩ source.1 source.2
  · exact sra_limb_result _ _ ⟨_,amount⟩ source.1 source.2

/-- All six decoded ordinary operations select their exact numerical reference. -/
theorem entry_selected_result {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (left w).Bounded) :
    (selectedWord w).Bounded ∧ (selectedWord w).toBitVec =
      entry.data.family.result (left w) (right w) := by
  cases family : entry.data.family
  · have contributions := entry_shift_contributions native fields query .sll family
    exact ⟨shift_selected_bounds contributions source,shift_selected_result contributions source⟩
  · have contributions := entry_shift_contributions native fields query .srl family
    exact ⟨shift_selected_bounds contributions source,shift_selected_result contributions source⟩
  · have contributions := entry_shift_contributions native fields query .sra family
    exact ⟨shift_selected_bounds contributions source,shift_selected_result contributions source⟩
  · have result := entry_binary_result native fields query .xor family
    exact ⟨result.selectedBound,result.selected⟩
  · have result := entry_binary_result native fields query .or family
    exact ⟨result.selectedBound,result.selected⟩
  · have result := entry_binary_result native fields query .and family
    exact ⟨result.selectedBound,result.selected⟩

/-- Actual selected and destination limbs are the canonical numerical result;
    original public decoding determines whether the destination is discarded. -/
theorem entry_numerical_result {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (left w).Bounded) :
    selectedWord w = Word.ofBitVec (entry.data.family.result (left w) (right w)) ∧
      writtenWord w = if entry.data.rd = 0 then ⟨0,0⟩ else
        Word.ofBitVec (entry.data.family.result (left w) (right w)) := by
  obtain ⟨bounded,bits⟩ := entry_selected_result native fields query source
  have selected : selectedWord w = Word.ofBitVec
      (entry.data.family.result (left w) (right w)) := by
    apply Word.eq_of_value bounded (Word.ofBitVec_bound _)
    rw [Word.ofBitVec_value,← bits,Word.toBitVec_toNat bounded]
  have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) query
  change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
  have masked := written_mask native (decide (entry.data.rd = 0))
    (by simpa only [decide_eq_true_eq] using flag)
  refine ⟨selected,?_⟩
  simpa only [decide_eq_true_eq,selected] using masked

end Airbender.ShiftBinop.Proofs
