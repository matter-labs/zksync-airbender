import Airbender.Proofs.SubwordMemory.LoadLow
import Airbender.Proofs.SubwordMemory.LoadHigh
import Airbender.Proofs.Mersenne31

namespace Airbender.SubwordMemory.LoadProofs
open Setup Verification
set_option autoImplicit false

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

/-- Source-shaped load outputs always fit two canonical 16-bit limbs. -/
theorem load_bounds (key : Nat) :
    (SubwordLoad.limbs key).1 < 65536 ∧ (SubwordLoad.limbs key).2 < 65536 := by
  have limb : key % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have lowByte : key % 65536 % 256 < 256 := Nat.mod_lt _ (by decide)
  have highByte : key % 65536 / 256 < 256 := by omega
  unfold SubwordLoad.limbs
  dsimp only
  split_ifs <;> dsimp <;> omega

/-- Every literal native row, retaining its exact compiled table tag. -/
theorem native_load_rows (i : Fin 2097152) :
    NativeSubwordLoad.data.rowNat i = (SubwordLoad.row i).push 45 := by
  have key : NativeSubwordLoad.data.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 2097152 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 0 1 i.val i.isLt
  have tag : NativeSubwordLoad.data.columns[3].get? i.val = some 45 := by
    change (⟨#[.affine 2097152 45 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 45 0 i.val i.isLt
  have low := low_output i
  have high := high_output i
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat, key, tag, low, high, SubwordLoad.row]

/-- Exact three-field Clean membership and literal native membership coincide. -/
theorem load_lookup (query : Vector (ZMod mersenne31Modulus) 3) :
    SubwordLoad.table.Contains #[] query ↔ ∃ i : Fin 2097152,
      query.push 45 = NativeSubwordLoad.data.row i := by
  change (∃ i : Fin 2097152, query = (SubwordLoad.row i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [TableData.row, native_load_rows, Vector.map_push]⟩
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    apply Vector.ext
    intro lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [TableData.row, native_load_rows, Vector.map_push,
      Vector.getElem_push, bound] using selected

/-- Native membership derives the full signed/unsigned output and both bounds. -/
theorem load_values {key low high : ZMod mersenne31Modulus}
    (member : SubwordLoad.table.Contains #[] #v[key, low, high]) :
    key.val < 2097152 ∧ low = ((SubwordLoad.limbs key.val).1 : Nat) ∧
      high = ((SubwordLoad.limbs key.val).2 : Nat) ∧ low.val < 65536 ∧ high.val < 65536 := by
  change ∃ i : Fin 2097152, #v[key, low, high] = (SubwordLoad.row i).map Nat.cast at member
  obtain ⟨i, same⟩ := member
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [SubwordLoad.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[0]) same
  have value : key.val = i.val := by
    rw [head, ZMod.val_natCast_of_lt (by have := i.isLt; unfold mersenne31Modulus; omega)]
  have lowEq : low = ((SubwordLoad.limbs key.val).1 : Nat) := by
    rw [value]
    simpa [SubwordLoad.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[1]) same
  have highEq : high = ((SubwordLoad.limbs key.val).2 : Nat) := by
    rw [value]
    simpa [SubwordLoad.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[2]) same
  have bounded := load_bounds key.val
  have fieldLarge : 65536 < mersenne31Modulus := by decide
  refine ⟨by rw [value]; exact i.isLt, lowEq, highEq, ?_, ?_⟩
  · rw [lowEq, ZMod.val_natCast_of_lt (lt_trans bounded.1 fieldLarge)]
    exact bounded.1
  · rw [highEq, ZMod.val_natCast_of_lt (lt_trans bounded.2 fieldLarge)]
    exact bounded.2

end Airbender.SubwordMemory.LoadProofs
