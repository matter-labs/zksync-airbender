import Airbender.Review.Helpers.Tables.NativeSubwordOffsetData
import Airbender.Review.Helpers.Tables.SubwordOffset
import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Proofs.Mersenne31
import Mathlib.Tactic.IntervalCases

namespace Airbender.SubwordMemory.Proofs
open Setup Verification
set_option autoImplicit false

-- Unchanged getter from the checked native v2 scalar certificate.
private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

private theorem periodic_zero_get (count n : Nat) (values : Array Nat)
    (size : values.size = 4) (bound : n < count * 4) :
    Block.get? (.periodic count 0 values) n = some (values[n % 4]?.getD 0) := by
  have result := Setup.Proofs.periodic_get values count 0 n (by omega) (by simpa only [size] using bound)
  simpa only [Int.natCast_zero, Nat.zero_mul, Nat.add_zero, size, Array.getElem?_eq_getElem (show n % 4 < values.size by omega), Option.getD_some] using result

private theorem periodic_skip (count n : Nat) (values : Array Nat) (rest : List Block)
    (size : values.size = 4) (bound : count * 4 ≤ n) :
    getFromBlocks (.periodic count 0 values :: rest) n = getFromBlocks rest (n - count * 4) := by
  rw [getFromBlocks]
  simp only [Block.length, size]
  rw [if_neg (by omega)]

private theorem periodic_head (count n : Nat) (values : Array Nat) (rest : List Block)
    (size : values.size = 4) (bound : n < count * 4) :
    getFromBlocks (.periodic count 0 values :: rest) n =
      some (values[n % 4]?.getD 0) := by
  rw [getFromBlocks]
  simp only [Block.length, size]
  rw [if_pos bound]
  exact periodic_zero_get count n values size bound

private abbrev nativeMaskBlocks : List Block :=
  [.periodic 16384 0 #[1, 1, 3, 3], .periodic 16384 0 #[1, 5, 3, 7], .periodic 16384 0 #[0, 4, 6, 6], .periodic 16384 0 #[4, 4, 6, 6], .periodic 16384 0 #[1, 1, 3, 3], .periodic 16384 0 #[1, 5, 3, 7], .periodic 32768 0 #[4, 4, 6, 6], .periodic 16384 0 #[1, 1, 3, 3], .periodic 16384 0 #[1, 5, 3, 7], .periodic 16384 0 #[0, 4, 6, 6], .periodic 16384 0 #[4, 4, 6, 6], .periodic 16384 0 #[1, 1, 3, 3], .periodic 16384 0 #[1, 5, 3, 7], .periodic 32768 0 #[4, 4, 6, 6], .periodic 16384 0 #[1, 1, 3, 3], .periodic 16384 0 #[1, 5, 3, 7], .periodic 16384 0 #[0, 4, 6, 6], .periodic 16384 0 #[4, 4, 6, 6], .periodic 16384 0 #[1, 1, 3, 3], .periodic 16384 0 #[1, 5, 3, 7], .periodic 32768 0 #[4, 4, 6, 6], .periodic 32768 0 #[1, 1, 3, 3], .periodic 16384 0 #[0, 0, 2, 2], .periodic 16384 0 #[4, 4, 6, 6], .periodic 32768 0 #[1, 1, 3, 3], .periodic 32768 0 #[4, 4, 6, 6]]

private theorem mask_group_0 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (0 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (0 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (0 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (0 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 0 := by omega
  have load : (0 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (0 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (0 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (0 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_1 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (1 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (1 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (1 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (1 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 1 := by omega
  have load : (1 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (1 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (1 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((1 * 65536 + a.val * 4 + b.val) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_2 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (2 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (2 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (2 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (2 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 2 := by omega
  have load : (2 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (2 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (2 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((2 * 65536 + a.val * 4 + b.val) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_3 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (3 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (3 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (3 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (3 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 3 := by omega
  have load : (3 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (3 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (3 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((3 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_4 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (4 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (4 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (4 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (4 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 4 := by omega
  have load : (4 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (4 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (4 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((4 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_5 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (5 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (5 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (5 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (5 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 5 := by omega
  have load : (5 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (5 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (5 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((5 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_6 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (6 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (6 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (6 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (6 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 6 := by omega
  have load : (6 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (6 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (6 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((6 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_7 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (7 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (7 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (7 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (7 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 7 := by omega
  have load : (7 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (7 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (7 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((7 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_8 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (8 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (8 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (8 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (8 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 0 := by omega
  have load : (8 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (8 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (8 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((8 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_9 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (9 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (9 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (9 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (9 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 1 := by omega
  have load : (9 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (9 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (9 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((9 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_10 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (10 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (10 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (10 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (10 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 2 := by omega
  have load : (10 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (10 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (10 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((10 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_11 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (11 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (11 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (11 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (11 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 3 := by omega
  have load : (11 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (11 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (11 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((11 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_12 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (12 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (12 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (12 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (12 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 4 := by omega
  have load : (12 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (12 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (12 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((12 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_13 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (13 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (13 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (13 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (13 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 5 := by omega
  have load : (13 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (13 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (13 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((13 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_14 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (14 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (14 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (14 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (14 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 6 := by omega
  have load : (14 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (14 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (14 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((14 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_15 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (15 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (15 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (15 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (15 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 7 := by omega
  have load : (15 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (15 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 0 := by omega
  change getFromBlocks nativeMaskBlocks (15 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((15 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_16 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (16 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (16 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (16 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (16 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 0 := by omega
  have load : (16 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (16 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (16 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((((16 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_17 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (17 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (17 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (17 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (17 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 1 := by omega
  have load : (17 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (17 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (17 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((((17 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_18 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (18 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (18 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (18 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (18 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 2 := by omega
  have load : (18 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (18 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (18 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((((((18 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_19 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (19 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (19 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (19 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (19 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 3 := by omega
  have load : (19 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (19 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (19 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((((((19 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_20 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (20 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (20 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (20 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (20 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 4 := by omega
  have load : (20 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (20 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (20 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((((((((20 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_21 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (21 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (21 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (21 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (21 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 5 := by omega
  have load : (21 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (21 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (21 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((((((((21 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_22 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (22 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (22 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (22 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (22 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 6 := by omega
  have load : (22 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (22 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (22 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((((((((((22 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_23 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (23 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (23 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (23 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (23 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 7 := by omega
  have load : (23 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 0 := by omega
  have zero : (23 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (23 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((((((((((23 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_24 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (24 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (24 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (24 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (24 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 0 := by omega
  have load : (24 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (24 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (24 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((((((((((24 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_25 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (25 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (25 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (25 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (25 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 1 := by omega
  have load : (25 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (25 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (25 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((((((((((25 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_26 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (26 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (26 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (26 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (26 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 2 := by omega
  have load : (26 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (26 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (26 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((((((((((((26 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 131072) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_27 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (27 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (27 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (27 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (27 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 3 := by omega
  have load : (27 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (27 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (27 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((((((((((((27 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 131072) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_28 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (28 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (28 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (28 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (28 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 4 := by omega
  have load : (28 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (28 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (28 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((((((((((((((28 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 131072) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_29 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (29 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (29 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (29 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (29 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 5 := by omega
  have load : (29 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (29 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (29 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : (((((((((((((((((((((((((29 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 131072) - 65536) - 65536) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_30 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (30 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (30 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (30 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (30 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 6 := by omega
  have load : (30 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (30 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (30 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((((((((((((((30 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 131072) - 65536) - 65536) - 131072) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_group_31 (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (31 * 65536 + a.val * 4 + b.val) = some (SubwordOffset.mask (31 * 65536 + a.val * 4 + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  have offset : (31 * 65536 + a.val * 4 + b.val) % 4 = b.val := by omega
  have funct3 : (31 * 65536 + a.val * 4 + b.val) / 65536 % 8 = 7 := by omega
  have load : (31 * 65536 + a.val * 4 + b.val) / 524288 % 2 = 1 := by omega
  have zero : (31 * 65536 + a.val * 4 + b.val) / 1048576 % 2 = 1 := by omega
  change getFromBlocks nativeMaskBlocks (31 * 65536 + a.val * 4 + b.val) = _
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_skip _ _ _ _ (by rfl) (by omega)]
  rw [periodic_head _ _ _ _ (by rfl) (by omega)]
  have selected : ((((((((((((((((((((((((((31 * 65536 + a.val * 4 + b.val) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 65536) - 65536) - 65536) - 65536) - 65536) - 65536) - 131072) - 131072) - 65536) - 65536) - 131072) % 4 = b.val := by omega
  simp only [selected]
  simp only [SubwordOffset.mask, offset, funct3, load, zero, SubwordOffset.validLoad]
  fin_cases b <;> norm_num

private theorem mask_grid (group : Fin 32) (a : Fin 16384) (b : Fin 4) :
    NativeSubwordOffset.data.columns[2].get? (group.val * 65536 + a.val * 4 + b.val) =
      some (SubwordOffset.mask (group.val * 65536 + a.val * 4 + b.val)) := by
  fin_cases group
  · exact mask_group_0 a b
  · exact mask_group_1 a b
  · exact mask_group_2 a b
  · exact mask_group_3 a b
  · exact mask_group_4 a b
  · exact mask_group_5 a b
  · exact mask_group_6 a b
  · exact mask_group_7 a b
  · exact mask_group_8 a b
  · exact mask_group_9 a b
  · exact mask_group_10 a b
  · exact mask_group_11 a b
  · exact mask_group_12 a b
  · exact mask_group_13 a b
  · exact mask_group_14 a b
  · exact mask_group_15 a b
  · exact mask_group_16 a b
  · exact mask_group_17 a b
  · exact mask_group_18 a b
  · exact mask_group_19 a b
  · exact mask_group_20 a b
  · exact mask_group_21 a b
  · exact mask_group_22 a b
  · exact mask_group_23 a b
  · exact mask_group_24 a b
  · exact mask_group_25 a b
  · exact mask_group_26 a b
  · exact mask_group_27 a b
  · exact mask_group_28 a b
  · exact mask_group_29 a b
  · exact mask_group_30 a b
  · exact mask_group_31 a b

private theorem exported_mask (n : Fin 2097152) :
    NativeSubwordOffset.data.columns[2].get? n.val = some (SubwordOffset.mask n.val) := by
  let group : Fin 32 := ⟨n.val / 65536, by omega⟩
  let a : Fin 16384 := ⟨n.val % 65536 / 4, by omega⟩
  let b : Fin 4 := ⟨n.val % 4, by omega⟩
  have same : group.val * 65536 + a.val * 4 + b.val = n.val := by
    dsimp [group, a, b]
    omega
  simpa only [same] using mask_grid group a b

/-- Every literal native row, including its compiled table tag. -/
theorem native_offset_rows (i : Fin 2097152) :
    NativeSubwordOffset.data.rowNat i = (SubwordOffset.row i).push 44 := by
  have key : NativeSubwordOffset.data.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 2097152 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 0 1 i.val i.isLt
  have offset : NativeSubwordOffset.data.columns[1].get? i.val = some (i.val % 4) := by
    change (⟨#[.periodic 524288 0 #[0, 1, 2, 3]]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt, periodic_zero_get 524288 i.val _ (by rfl) i.isLt]
    have values : ∀ k : Fin 4, (#[0, 1, 2, 3][k.val]?.getD 0) = k.val := by decide +kernel
    exact congrArg some (values ⟨i.val % 4, by omega⟩)
  have tag : NativeSubwordOffset.data.columns[3].get? i.val = some 44 := by
    change (⟨#[.affine 2097152 44 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 44 0 i.val i.isLt
  have result := exported_mask i
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat, key, offset, result, tag, SubwordOffset.row]

/-- Native literal-data membership and the original Clean table have the same
    exact three fields, with the native tag retained on the exported side. -/
theorem offset_lookup (query : Vector (ZMod mersenne31Modulus) 3) :
    SubwordOffset.table.Contains #[] query ↔ ∃ i : Fin 2097152,
      query.push 44 = NativeSubwordOffset.data.row i := by
  change (∃ i : Fin 2097152, query = (SubwordOffset.row i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [TableData.row, native_offset_rows, Vector.map_push]⟩
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    apply Vector.ext
    intro lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [TableData.row, native_offset_rows, Vector.map_push,
      Vector.getElem_push, bound] using selected

/-- Canonical key/offset and the complete native width, limb and trap bitmask. -/
theorem offset_values {key offset mask : ZMod mersenne31Modulus}
    (holds : SubwordOffset.table.Contains #[] #v[key, offset, mask]) :
    key.val < 2097152 ∧ offset = (key.val % 4 : Nat) ∧
      mask = (SubwordOffset.mask key.val : Nat) := by
  change ∃ i : Fin 2097152, #v[key, offset, mask] = (SubwordOffset.row i).map Nat.cast at holds
  obtain ⟨i, same⟩ := holds
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [SubwordOffset.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[0]) same
  have value : key.val = i.val := by
    rw [head, ZMod.val_natCast_of_lt (by have := i.isLt; unfold mersenne31Modulus; omega)]
  refine ⟨by rw [value]; exact i.isLt, ?_, ?_⟩
  · rw [value]
    simpa [SubwordOffset.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[1]) same
  · rw [value]
    simpa [SubwordOffset.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[2]) same

end Airbender.SubwordMemory.Proofs
