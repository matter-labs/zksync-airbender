import Airbender.Proofs.SubwordMemory.ByteMath
import Airbender.Proofs.SubwordMemory.PackedKeys

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option autoImplicit false

/-- Interpret the exact v2 raw-funct3 packed key using Sail's own extension.
    Odd halfword rows retain native zero outputs; alignment is derived later. -/
theorem packed_load_extension (byte unsigned : Bool) {half offset : Nat}
    (halfBound : half < 65536) (offsetBound : offset < 4)
    (aligned : byte = false → offset % 2 = 0) :
    let funct3 := (if byte then 0 else 1) + (if unsigned then 4 else 0)
    let result := SubwordLoad.limbs (half + 65536 * offset + 262144 * funct3)
    (⟨result.1,result.2⟩ : Word).Bounded ∧ (⟨result.1,result.2⟩ : Word).toBitVec =
      if byte then SailRV32.Functions.extend_value unsigned
        (BitVec.ofNat 8 (half / (if offset % 2 = 0 then 1 else 256)))
      else SailRV32.Functions.extend_value unsigned (BitVec.ofNat 16 half) := by
  dsimp only
  have functBound : (if byte then 0 else 1) + (if unsigned then 4 else 0) < 8 := by
    cases byte <;> cases unsigned <;> decide
  obtain ⟨limb,position,funct⟩ := packed_parts halfBound offsetBound functBound
  let value := if byte then (if offset % 2 = 0 then half % 256 else half / 256) else half
  have valueBound : value < (if byte then 256 else 65536) := by
    cases byte
    · exact halfBound
    · dsimp [value]; split_ifs <;> omega
  have extension := extend_subword_limbs byte (!unsigned) value valueBound
  have canonical (n : Nat) : BitVec.ofNat 8 (n % 256) = BitVec.ofNat 8 n := by
    apply BitVec.eq_of_toNat_eq
    simp
  simp only [SubwordLoad.limbs,limb,position,funct]
  cases byte <;> cases unsigned
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true,Nat.reduceAdd,Nat.reduceEqDiff]
    simp only [value,Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true] at extension
    try rw [canonical] at extension
    first
    | (rw [aligned rfl]; simpa using extension)
    | (split_ifs at extension ⊢ <;> simp_all [Nat.div_one] <;> omega)

/-- A preselected v2 limb/offset is exactly the byte or halfword slice of the
    bounded native word. Reuse unchanged v3 arithmetic extraction, not its keys. -/
theorem word_load_extension (byte unsigned highHalf highByte : Bool)
    (word : Word) (wordBound : word.Bounded)
    (aligned : byte = false → highByte = false) :
    let offset : Nat := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    let half := if highHalf then word.hi else word.lo
    let funct3 := (if byte then 0 else 1) + (if unsigned then 4 else 0)
    let result := SubwordLoad.limbs (half + 65536 * offset + 262144 * funct3)
    (⟨result.1,result.2⟩ : Word).Bounded ∧ (⟨result.1,result.2⟩ : Word).toBitVec =
      SailRV32.Functions.extend_value unsigned
        ((word.toBitVec >>> (8 * offset)).setWidth (8 * (if byte then 1 else 2))) := by
  let offset : Nat := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
  have offsetBound : offset < 4 := by cases highByte <;> cases highHalf <;> decide
  have halfBound : (if highHalf then word.hi else word.lo) < 65536 := by
    cases highHalf <;> first | exact wordBound.1 | exact wordBound.2
  have parity : byte = false → offset % 2 = 0 := by
    intro half
    have low := aligned half
    cases highByte <;> cases highHalf <;> simp_all [offset]
  have extension := packed_load_extension byte unsigned halfBound offsetBound parity
  have extract := subword_extract byte highHalf highByte word wordBound aligned
  refine ⟨extension.1,?_⟩
  rw [extension.2]
  cases byte <;> cases highHalf <;> cases highByte
  all_goals first
    | (have impossible := aligned rfl; contradiction)
    | (simpa [offset] using congrArg (SailRV32.Functions.extend_value unsigned) extract.symm)

end Airbender.SubwordMemory.Proofs
