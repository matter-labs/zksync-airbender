import Airbender.Proofs.SubwordMemory.DataControls
import Airbender.Proofs.SubwordMemory.ROMAddress
import Airbender.Proofs.SubwordMemory.LoadExtension

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option autoImplicit false

/-- Actual upper selection, after native Boolean and fixed-offset controls. -/
theorem selected_word {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (low high : Nat) : (selectedLimb w low high).val =
      if 2 ≤ (w 22).val then (w high).val else (w low).val := by
  have upper := (accepted_offset_values native).upper
  have small : (w 22).val < 4 := by rw [(accepted_offset_values native).offset]; exact Nat.mod_lt _ (by decide)
  rcases upper_bit native with lower | higher
  · have selected : ¬ 2 ≤ (w 22).val := by rw [lower] at upper; norm_num at upper; omega
    simp [selectedLimb,lower,selected]
  · have selected : 2 ≤ (w 22).val := by
      rw [higher] at upper
      have one : (1 : ZMod mersenne31Modulus).val = 1 := by decide +kernel
      rw [one] at upper
      omega
    simp [selectedLimb,higher,selected]

/-- Exact native data-query outputs are the original Sail extension of the
    actual bounded word slice. The native key and both offset bits are derived. -/
theorem native_load_result {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    {low high : Nat} (byte unsigned : Bool)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (values : LoadValues w (dataKey w (selectedLimb w low high)))
    (wordBound : (⟨(w low).val,(w high).val⟩ : Word).Bounded)
    (raw : (w 11).val = (if byte then 0 else 1) + (if unsigned then 4 else 0))
    (aligned : byte = false → (w 22).val % 2 = 0) :
    (⟨(w 60).val,(w 61).val⟩ : Word).toBitVec =
      SailRV32.Functions.extend_value unsigned
        (((⟨(w low).val,(w high).val⟩ : Word).toBitVec >>> (8 * (w 22).val)).setWidth
          (8 * (if byte then 1 else 2))) := by
  let upper : Bool := decide (2 ≤ (w 22).val)
  let lower : Bool := decide ((w 22).val % 2 = 1)
  have offsetBound : (w 22).val < 4 := by rw [(accepted_offset_values native).offset]; exact Nat.mod_lt _ (by decide)
  have bits : (if lower then 1 else 0) + 2 * (if upper then 1 else 0) = (w 22).val := by
    simp only [lower,upper,decide_eq_true_eq]
    split_ifs <;> omega
  have alignBits : byte = false → lower = false := by
    intro half
    have even := aligned half
    simp [lower,even]
  have extension := word_load_extension byte unsigned upper lower
    (⟨(w low).val,(w high).val⟩ : Word) wordBound alignBits
  dsimp only at extension
  rw [bits] at extension
  have functBound : (w 11).val < 8 := by rw [raw]; cases byte <;> cases unsigned <;> decide
  have key := native_data_key (selected_limb_bound native wordBound) offsetBound functBound
  rw [selected_word native low high,raw] at key
  have sameHalf : (if upper then (w high).val else (w low).val) =
      if 2 ≤ (w 22).val then (w high).val else (w low).val := by simp only [upper,decide_eq_true_eq]
  rw [sameHalf] at extension
  have lowValue := values.low
  have highValue := values.high
  rw [key] at lowValue highValue
  have candidates : (⟨(w 60).val,(w 61).val⟩ : Word) =
      ⟨(SubwordLoad.limbs ((if 2 ≤ (w 22).val then (w high).val else (w low).val) +
        65536 * (w 22).val + 262144 * ((if byte then 0 else 1) + (if unsigned then 4 else 0)))).1,
       (SubwordLoad.limbs ((if 2 ≤ (w 22).val then (w high).val else (w low).val) +
        65536 * (w 22).val + 262144 * ((if byte then 0 else 1) + (if unsigned then 4 else 0)))).2⟩ := by
    rw [lowValue,highValue,ZMod.val_natCast_of_lt (lt_trans extension.1.1 (by decide)),
      ZMod.val_natCast_of_lt (lt_trans extension.1.2 (by decide))]
  rw [candidates]
  exact extension.2

/-- Original decoded metadata and native masked writes retain discarded x0
    loads. Retained loads use the actual RAM word or exact native ROM word index. -/
theorem entry_load_effect {rom : WordROM} {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (geometry : NativeAddress w) (fields : DecodedFields w entry)
    (bound : (dataWord w).Bounded) :
    entry.data.family.mask = 0 → (writtenWord w).toBitVec = if entry.data.rd = 0 then 0 else
      SailRV32.Functions.extend_value entry.data.family.unsigned
        (((loadWord rom w).toBitVec >>> (8 * (w 22).val)).setWidth (8 * entry.data.family.width)) := by
  intro isLoad
  have load : w 12 = 0 := by simpa only [isLoad,Nat.cast_zero] using fields.store
  obtain ⟨lowWrite,highWrite⟩ := load_write_mask native load
  by_cases discarded : entry.data.rd = 0
  · have zero : w 8 = 1 := by simpa only [discarded,if_true] using fields.zero
    simp [writtenWord,lowWrite,highWrite,zero,discarded,Word.toBitVec,Word.value]
  · have zero : w 8 = 0 := by simpa only [discarded,if_false] using fields.zero
    simp only [zero,sub_zero,one_mul] at lowWrite highWrite
    rw [if_neg discarded]
    have raw : (w 11).val = (if entry.data.family.byte then 0 else 1) +
        (if entry.data.family.unsigned then 4 else 0) := by
      rw [(entry_raw_values fields).2.1]
      cases entry.data.family <;> decide
    have aligned := (entry_data_controls native fields).2.2.2
    have parity : entry.data.family.byte = false → (w 22).val % 2 = 0 :=
      fun half => aligned half (Or.inr discarded)
    change (⟨(w 39).val,(w 40).val⟩ : Word).toBitVec = _
    rw [lowWrite,highWrite]
    by_cases range : (w 20).val < 64
    · have word := native_rom_word native geometry load range
      have romBound : (⟨(w 41).val,(w 42).val⟩ : Word).Bounded := by rw [word]; exact Word.ofBitVec_bound _
      have result := native_load_result _ _ native (rom_load_values native load range).2 romBound raw parity
      simpa only [loadWord,range,if_true,← word,Operation.width] using result
    · have result := native_load_result _ _ native (ram_load_values native load (by omega)) bound raw parity
      simpa only [loadWord,range,if_false,dataWord,Operation.width] using result

end Airbender.SubwordMemory.Proofs
