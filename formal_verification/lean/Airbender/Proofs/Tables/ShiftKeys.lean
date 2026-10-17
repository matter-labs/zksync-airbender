import Airbender.Review.Helpers.Tables.Shift.Column0
import Airbender.Review.Helpers.Tables.Shift.Column1
import Airbender.Review.Helpers.Tables.Shift.Column2
import Airbender.Review.Helpers.Tables.Shift.Column3
import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.Tables.AlignedConstants

namespace Airbender.Verification.ShiftKeys
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem constant_get (length value n : Nat) (bound : n < length) :
    Block.get? (.affine length value 0) n = some value := by
  simp [Block.get?, Block.length, bound]

private theorem unit_get (length first n : Nat) (bound : n < length) :
    Block.get? (.affine length first 1) n = some (first + n) := by
  simp [Block.get?, Block.length, bound]
  simpa only [Int.natCast_add] using
    And.intro (Int.natCast_nonneg (first + n)) (Int.toNat_natCast (first + n))

theorem repeated_get (block : Block)
    (count n : Nat) (bound : n < count * block.length) :
    getFromBlocks (List.replicate count block) n = block.get? (n % block.length) := by
  induction count generalizing n with
  | zero => simp at bound
  | succ count ih =>
    simp only [Nat.succ_mul] at bound
    by_cases inside : n < block.length
    · simp only [List.replicate_succ, getFromBlocks, if_pos inside, Nat.mod_eq_of_lt inside]
    · have remaining : n - block.length < count * block.length := by omega
      rw [List.replicate_succ, getFromBlocks, if_neg inside, ih _ remaining,
        ← Nat.mod_eq_sub_mod (Nat.le_of_not_gt inside)]

private theorem four_get (block : Block) (length : block.length = 65536)
    (n : Nat) (bound : n < 262144) :
    getFromBlocks [block, block, block, block] n = block.get? (n % 65536) := by
  have extent : n < 4 * block.length := by rw [length]; omega
  simpa only [List.replicate_succ, List.replicate_zero, length] using
    repeated_get block 4 n extent

private theorem position_aligned : Setup.Proofs.AlignedConstants
    byteShiftColumn0.blocks.toList := by decide +kernel
private theorem position_samples : ∀ q : Fin 8,
    byteShiftColumn0.get? (q.val * 32768) = some (q.val / 2) := by
  intro q
  fin_cases q <;> decide +kernel

theorem position (n : Nat) (bound : n < 262144) :
    byteShiftColumn0.get? n = some (n / 65536) := by
  have aligned := Setup.Proofs.alignedConstants_get _ position_aligned n
  have sample := position_samples ⟨n / 32768, by omega⟩
  have value : n / 32768 / 2 = n / 65536 := by omega
  exact aligned.trans (sample.trans (congrArg some value))

private theorem ascending_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 1 (Array.replicate 256 0)) n = some (n / 256) := by
  have hm : n % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [Block.get?, Block.length, bound, hm]
  simpa only [Int.natCast_ediv, Nat.cast_ofNat] using
    And.intro (Int.natCast_nonneg (n / 256)) (Int.toNat_natCast (n / 256))

theorem byte (n : Nat) (bound : n < 262144) :
    byteShiftColumn1.get? n = some (n / 256 % 256) := by
  let block := Block.periodic 256 1 (Array.replicate 256 0)
  change getFromBlocks [block, block, block, block] n = _
  rw [four_get block (by decide) n bound]
  have row := ascending_get (n % 65536) (Nat.mod_lt _ (by decide))
  have value : (n % 65536) / 256 = n / 256 % 256 := by omega
  exact row.trans (congrArg some value)

private def amountValues : Array Nat :=
  match (byteShiftColumn2.blocks[0]? : Option Setup.Block) with
  | some (Setup.Block.periodic _ _ values) => values
  | _ => #[]
private theorem amount_size : amountValues.size = 256 := by decide +kernel
private theorem amount_samples (q : Fin 256) :
    amountValues[q.val]'(by rw [amount_size]; exact q.isLt) = q.val / 8 := by
  simp [amountValues, byteShiftColumn2]
private theorem amount_column : byteShiftColumn2 =
    Column.mk #[.periodic 1024 0 amountValues] := rfl

private theorem periodic_zero_get (count n : Nat) (values : Array Nat)
    (positive : 0 < values.size) (bound : n < count * values.size) :
    Block.get? (.periodic count 0 values) n =
      some (values[n % values.size]'(Nat.mod_lt _ positive)) := by
  have hm : n % values.size < values.size := Nat.mod_lt _ positive
  simp [Block.get?, Block.length, bound, hm]

theorem amount (n : Nat) (bound : n < 262144) :
    byteShiftColumn2.get? n = some (n / 8 % 32) := by
  have positive : 0 < amountValues.size := by rw [amount_size]; decide
  have extent : n < 1024 * amountValues.size := by rw [amount_size]; omega
  have sampled := amount_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  have value : (n % 256) / 8 = n / 8 % 32 := by omega
  rw [amount_column]
  simp only [Column.get?, getFromBlocks, Block.length, if_pos extent]
  rw [periodic_zero_get _ _ _ positive extent]
  simpa only [amount_size, sampled] using congrArg some value

private theorem cyclic_get (count n : Nat) (bound : n < count * 8) :
    Block.get? (.periodic count 0 (Array.ofFn (fun i : Fin 8 => (1 + i.val) % 8))) n =
      some ((1 + n % 8) % 8) := by
  have hm : n % 8 < 8 := Nat.mod_lt _ (by decide)
  simp [Block.get?, Block.length, bound, hm]
  simpa only [Int.natCast_emod, Int.natCast_add, Int.natCast_one, Nat.cast_ofNat] using
    And.intro (Int.natCast_nonneg ((1 + n) % 8)) (Int.toNat_natCast ((1 + n) % 8))

theorem operation (n : Nat) (bound : n < 262144) :
    byteShiftColumn3.get? n = some (n % 8) := by
  change getFromBlocks [.affine 1 0 0,
    .periodic 32767 0 (Array.ofFn (fun i : Fin 8 => (1 + i.val) % 8)),
    .affine 7 1 1] n = _
  by_cases zero : n = 0
  · simp [zero, getFromBlocks, Block.get?, Block.length]
  · have first : ¬ n < 1 := by omega
    by_cases middle : n < 262137
    · have extent : n - 1 < 32767 * 8 := by omega
      simp only [getFromBlocks, Block.length, Array.size_ofFn, Nat.reduceMul,
        if_neg first, if_pos extent]
      have value : (1 + (n - 1) % 8) % 8 = n % 8 := by omega
      exact (cyclic_get _ _ extent).trans (congrArg some value)
    · have period : ¬ n - 1 < 262136 := by omega
      have tail : n - 1 - 262136 < 7 := by omega
      simp only [getFromBlocks, Block.length, Array.size_ofFn, Nat.reduceMul,
        if_neg first, if_neg period, if_pos tail]
      have value : 1 + (n - 1 - 262136) = n % 8 := by omega
      exact (unit_get 7 1 _ tail).trans (congrArg some value)

end Airbender.Verification.ShiftKeys
