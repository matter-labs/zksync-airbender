import Airbender.Review.Circuits.SubwordMemory.DataModel
import Airbender.Proofs.SubwordMemory.Address

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option autoImplicit false

/-- Recover the three native offset-table metadata fields without field wrap. -/
theorem offset_key_parts {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (functBound : (w 11).val < 8) (zeroBit : w 8 = 0 ∨ w 8 = 1) :
    (offsetKey w).val / 65536 % 8 = (w 11).val ∧
    (offsetKey w).val / 524288 % 2 = 1 - (w 12).val ∧
    (offsetKey w).val / 1048576 % 2 = (w 8).val := by
  have low := (address_bounds native).1
  change (w 19).val < 65536 at low
  have zero := boolean_val zeroBit
  have store := boolean_val (store_bit native)
  rw [native_offset_key native functBound zeroBit]
  omega

/-- Raw native ranges and flags come from the original decoded entry. -/
theorem entry_raw_values {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (fields : DecodedFields w entry) :
    (w 12).val = entry.data.family.mask ∧ (w 11).val = entry.data.family.funct3 ∧
    (w 8).val = if entry.data.rd = 0 then 1 else 0 := by
  refine ⟨?_,?_,?_⟩
  · rw [fields.store,ZMod.val_natCast_of_lt (by cases entry.data.family <;> decide)]
  · rw [fields.funct3,ZMod.val_natCast_of_lt (by cases entry.data.family <;> decide)]
  · rw [fields.zero]
    split_ifs <;> decide +kernel

/-- Every supported byte/halfword metadata value selects the native subword mux. -/
theorem supported_mask_size (operation : Operation) {key : Nat}
    (funct : key / 65536 % 8 = operation.funct3) : SubwordOffset.mask key % 2 = 1 := by
  unfold SubwordOffset.mask
  rw [funct]
  cases operation
  all_goals simp only [Operation.funct3,Nat.reduceBEq,Bool.or_true,Bool.true_or,if_true]
  all_goals split_ifs <;> omega

/-- Absence of the native trap bit forces retained/store halfwords to align.
    Discarded loads keep the original native waiver. -/
theorem supported_mask_alignment (operation : Operation) (discarded : Bool) {key : Nat}
    (funct : key / 65536 % 8 = operation.funct3)
    (load : key / 524288 % 2 = 1 - operation.mask)
    (zero : key / 1048576 % 2 = if discarded then 1 else 0)
    (trap : SubwordOffset.mask key < 4)
    (half : operation.byte = false) (retained : operation.mask = 1 ∨ discarded = false) :
    key % 4 % 2 = 0 := by
  simp only [SubwordOffset.mask,funct,load,zero] at trap
  cases operation <;> cases discarded
  all_goals simp [Operation.byte,Operation.mask] at half retained
  all_goals simp [Operation.funct3,Operation.mask,SubwordOffset.validLoad] at trap
  all_goals split_ifs at trap <;> omega

/-- Native subword size/upper selectors are derived. Halfword accesses align
    when retained or stored; the exact native discarded-load waiver is preserved. -/
theorem entry_data_controls {rom : WordROM} {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (fields : DecodedFields w entry) :
    w 24 = 1 ∧ (w 22).val < 4 ∧ (w 25).val = (w 22).val / 2 ∧
      (entry.data.family.byte = false → (entry.data.family.mask = 1 ∨ entry.data.rd ≠ 0) →
        (w 22).val % 2 = 0) := by
  have raw := entry_raw_values fields
  have functBound : (w 11).val < 8 := by rw [raw.2.1]; cases entry.data.family <;> decide
  have zeroBit : w 8 = 0 ∨ w 8 = 1 := by
    rw [fields.zero]
    split_ifs <;> simp
  obtain ⟨funct,load,zero⟩ := offset_key_parts native functBound zeroBit
  have functValue := funct.trans raw.2.1
  have loadValue : (offsetKey w).val / 524288 % 2 = 1 - entry.data.family.mask := by rw [load,raw.1]
  have zeroValue : (offsetKey w).val / 1048576 % 2 = if decide (entry.data.rd = 0) then 1 else 0 := by
    simpa only [decide_eq_true_eq] using zero.trans raw.2.2
  have controls := accepted_offset_values native
  have small : (w 22).val < 4 := by rw [controls.offset]; exact Nat.mod_lt _ (by decide)
  have sizeOne : (w 24).val = 1 := controls.size.trans (supported_mask_size _ functValue)
  refine ⟨?_,small,controls.upper,?_⟩
  · have same := congrArg (fun n : Nat => (n : ZMod mersenne31Modulus)) sizeOne
    simpa using same
  · intro half retained
    rw [controls.offset]
    apply supported_mask_alignment _ _ functValue loadValue zeroValue controls.trapAbsent half
    rcases retained with store | nonzero
    · exact Or.inl store
    · exact Or.inr (by simp only [decide_eq_false_iff_not]; exact nonzero)

end Airbender.SubwordMemory.Proofs
