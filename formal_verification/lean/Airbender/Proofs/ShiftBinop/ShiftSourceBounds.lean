import Airbender.Proofs.ShiftBinop.ShiftContributions
import Airbender.Proofs.ShiftBinop.SllLimbBounds
import Airbender.Proofs.ShiftBinop.SrlLimbBounds
import Airbender.Proofs.ShiftBinop.SraLimbBounds

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Bounded source limbs make the native packed-key field equation canonical.
    This is an internal calculation; initialized range induction supplies bounds. -/
theorem canonical_shift_key (source amount key : ZMod mersenne31Modulus)
    (sourceBound : source.val < 65536) (amountBound : amount.val < 32)
    (equation : key = source + 65536 * amount) :
    key.val = source.val + 65536 * amount.val ∧
      key.val % 65536 = source.val ∧ key.val / 65536 = amount.val := by
  have small : source.val + 65536 * amount.val < mersenne31Modulus := by
    change _ < 2147483647
    omega
  have field : ((source.val + 65536 * amount.val : Nat) : ZMod mersenne31Modulus) = key := by
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
    exact equation.symm
  have natural := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt small] at natural
  refine ⟨natural.symm,?_,?_⟩ <;> omega

private theorem part_word {w : Nat → ZMod mersenne31Modulus} {kind : ShiftKind}
    (contributions : ShiftContributions w kind) (slot : Fin 3) :
    partWord w slot = Word.ofBitVec ((kind.parts[slot.val]).result (w (43 + 4 * slot.val)).val) := by
  have bound := (contributions.parts slot).2.1
  have value := congrArg BitVec.toNat (contributions.parts slot).2.2
  rw [Word.toBitVec_toNat bound] at value
  apply Word.eq_of_value bound (Word.ofBitVec_bound _)
  rw [Word.ofBitVec_value]
  exact value

/-- Actual accepted native contribution words agree with their bounded-source
    reference pieces; no table-equivalence or desired-output premise is used. -/
theorem shift_part_words {w : Nat → ZMod mersenne31Modulus} {kind : ShiftKind}
    (contributions : ShiftContributions w kind) (source : (left w).Bounded)
    (slot : Fin 3) :
    partWord w slot = Word.ofBitVec (limbPieces kind (left w).lo (left w).hi (w 29).val)[slot.val] := by
  have amount : (w 29).val < 32 := by rw [contributions.amount]; exact Nat.mod_lt _ (by decide)
  cases kind <;> fin_cases slot
  · have key : w 43 = w 23 + 65536 * w 29 := by
      simpa [ShiftKind.parts,ShiftKind.sourceColumn] using contributions.keys 0
    have canonical := canonical_shift_key (w 23) (w 29) (w 43) source.1 amount key
    have result := part_word contributions 0
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,canonical.2.1,canonical.2.2,left] using result
  · have key : w 47 = w 24 + 65536 * w 29 := by
      simpa [ShiftKind.parts,ShiftKind.sourceColumn] using contributions.keys 1
    have canonical := canonical_shift_key (w 24) (w 29) (w 47) source.2 amount key
    have result := part_word contributions 1
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,canonical.2.1,canonical.2.2,left] using result
  · have key : w 51 = 0 := by
      simpa [ShiftKind.parts] using contributions.keys 2
    have result := part_word contributions 2
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,key] using result
  · have key : w 43 = w 23 + 65536 * w 29 := by
      simpa [ShiftKind.parts,ShiftKind.sourceColumn] using contributions.keys 0
    have canonical := canonical_shift_key (w 23) (w 29) (w 43) source.1 amount key
    have result := part_word contributions 0
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,canonical.2.1,canonical.2.2,left] using result
  · have key : w 47 = w 24 + 65536 * w 29 := by
      simpa [ShiftKind.parts,ShiftKind.sourceColumn] using contributions.keys 1
    have canonical := canonical_shift_key (w 24) (w 29) (w 47) source.2 amount key
    have result := part_word contributions 1
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,canonical.2.1,canonical.2.2,left] using result
  · have key : w 51 = 0 := by
      simpa [ShiftKind.parts] using contributions.keys 2
    have result := part_word contributions 2
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,key] using result
  · have key : w 43 = w 24 + 65536 * w 29 := by
      simpa [ShiftKind.parts,ShiftKind.sourceColumn] using contributions.keys 0
    have canonical := canonical_shift_key (w 24) (w 29) (w 43) source.2 amount key
    have result := part_word contributions 0
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,canonical.2.1,canonical.2.2,left] using result
  · have key : w 47 = w 23 + 65536 * w 29 := by
      simpa [ShiftKind.parts,ShiftKind.sourceColumn] using contributions.keys 1
    have canonical := canonical_shift_key (w 23) (w 29) (w 47) source.1 amount key
    have result := part_word contributions 1
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,canonical.2.1,canonical.2.2,left] using result
  · have key : w 51 = w 24 + 65536 * w 29 := by
      simpa [ShiftKind.parts,ShiftKind.sourceColumn] using contributions.keys 2
    have canonical := canonical_shift_key (w 24) (w 29) (w 51) source.2 amount key
    have result := part_word contributions 2
    simpa [limbPieces,ShiftKind.parts,ShiftPart.result,canonical.2.1,canonical.2.2,left] using result

/-- Disjoint native contribution halves give canonical selected limbs once the
    initialized source read is bounded. The shared history induction removes
    this local source premise from the public trace claim. -/
theorem shift_selected_bounds {w : Nat → ZMod mersenne31Modulus} {kind : ShiftKind}
    (contributions : ShiftContributions w kind) (source : (left w).Bounded) :
    (selectedWord w).Bounded := by
  have amount : (w 29).val < 32 := by rw [contributions.amount]; exact Nat.mod_lt _ (by decide)
  have parts := shift_part_words contributions source
  have assembled : selectedWord w = piecesWord (limbPieces kind (left w).lo (left w).hi (w 29).val) := by
    apply congrArg₂ Word.mk
    · rw [contributions.selectedLow]
      change (partWord w 0).lo + (partWord w 1).lo + (partWord w 2).lo = _
      rw [parts 0,parts 1,parts 2]
      rfl
    · rw [contributions.selectedHigh]
      change (partWord w 0).hi + (partWord w 1).hi + (partWord w 2).hi = _
      rw [parts 0,parts 1,parts 2]
      rfl
  rw [assembled]
  cases kind
  · exact sll_limb_bounds _ _ ⟨_,amount⟩ source.1 source.2
  · exact srl_limb_bounds _ _ ⟨_,amount⟩ source.1 source.2
  · exact sra_limb_bounds _ _ ⟨_,amount⟩ source.1 source.2

end Airbender.ShiftBinop.Proofs
