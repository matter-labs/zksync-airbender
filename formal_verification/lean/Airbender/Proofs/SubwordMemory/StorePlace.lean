import Airbender.Review.Helpers.Tables.NativeSubwordStorePlaceData
import Airbender.Review.Helpers.Tables.SubwordStorePlace
import Airbender.Proofs.SubwordMemory.LoadGetters
import Airbender.Proofs.Mersenne31

namespace Airbender.SubwordMemory.StorePlaceProofs
open Setup Verification Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

private def highValues : Array Nat := NativeSubwordStorePlace.dataValues1_1

private theorem high_size : highValues.size = 256 := by
  simp only [highValues, NativeSubwordStorePlace.dataValues1_1, Array.size_ofFn]

private theorem high_samples (i : Fin 256) :
    highValues[i.val]?.getD 0 = 256 * i.val := by
  simp [highValues, NativeSubwordStorePlace.dataValues1_1, i.isLt]

private theorem place_blocks : NativeSubwordStorePlace.data.columns[1].blocks.toList =
    [.periodic 256 0 (Array.range 256), .periodic 256 0 highValues,
     .periodic 256 0 (Array.range 256), .periodic 256 0 highValues,
     .affine 65536 0 1, .affine 65536 0 1, .affine 65536 0 1, .affine 65536 0 1,
     .affine 1572864 0 0] := rfl

private theorem periodic_nat (values : Array Nat) (count stride n : Nat)
    (positive : 0 < values.size) (bound : n < count * values.size) :
    Block.get? (.periodic count (stride : Int) values) n =
      some (values[n % values.size]?.getD 0 + stride * (n / values.size)) := by
  have read := Setup.Proofs.periodic_get values count stride n positive bound
  simpa only [Array.getElem?_eq_getElem (Nat.mod_lt n positive), Option.getD_some] using read

private theorem high_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 0 highValues) n = some (256 * (n % 256)) := by
  have read := periodic_nat highValues 256 0 n (by rw [high_size]; decide)
    (by rw [high_size]; omega)
  have sample := high_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [Int.natCast_zero, high_size, Nat.zero_mul, Nat.add_zero, sample] using read

private theorem place_length_0 : (.periodic 256 0 (Array.range 256) : Block).length = 65536 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_length_1 : (.periodic 256 0 highValues : Block).length = 65536 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_length_2 : (.periodic 256 0 (Array.range 256) : Block).length = 65536 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_length_3 : (.periodic 256 0 highValues : Block).length = 65536 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_length_4 : (.affine 65536 0 1 : Block).length = 65536 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_length_5 : (.affine 65536 0 1 : Block).length = 65536 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_length_6 : (.affine 65536 0 1 : Block).length = 65536 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_length_7 : (.affine 65536 0 1 : Block).length = 65536 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_length_8 : (.affine 1572864 0 0 : Block).length = 1572864 := by norm_num only [Block.length, Array.size_range, high_size]

private theorem place_group_0 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (0 * 65536 + x.val) = some (SubwordStorePlace.placed (0 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (0 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (0 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (0 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (0 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_head _ _ _ _ place_length_0 (by omega)]
  rw [range_get _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_1 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (1 * 65536 + x.val) = some (SubwordStorePlace.placed (1 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (1 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (1 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (1 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (1 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_head _ _ _ _ place_length_1 (by omega)]
  rw [high_get _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_2 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (2 * 65536 + x.val) = some (SubwordStorePlace.placed (2 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (2 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (2 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (2 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (2 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_head _ _ _ _ place_length_2 (by omega)]
  rw [range_get _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem place_group_3 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (3 * 65536 + x.val) = some (SubwordStorePlace.placed (3 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (3 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (3 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (3 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (3 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_head _ _ _ _ place_length_3 (by omega)]
  rw [high_get _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem place_group_4 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (4 * 65536 + x.val) = some (SubwordStorePlace.placed (4 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (4 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (4 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (4 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (4 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_head _ _ _ _ place_length_4 (by omega)]
  rw [affine_one_get 65536 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem place_group_5 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (5 * 65536 + x.val) = some (SubwordStorePlace.placed (5 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (5 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (5 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (5 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (5 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_head _ _ _ _ place_length_5 (by omega)]
  rw [affine_one_get 65536 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem place_group_6 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (6 * 65536 + x.val) = some (SubwordStorePlace.placed (6 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (6 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (6 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (6 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (6 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_head _ _ _ _ place_length_6 (by omega)]
  rw [affine_one_get 65536 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem place_group_7 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (7 * 65536 + x.val) = some (SubwordStorePlace.placed (7 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (7 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (7 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (7 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (7 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_head _ _ _ _ place_length_7 (by omega)]
  rw [affine_one_get 65536 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem place_group_8 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (8 * 65536 + x.val) = some (SubwordStorePlace.placed (8 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (8 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (8 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (8 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (8 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_9 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (9 * 65536 + x.val) = some (SubwordStorePlace.placed (9 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (9 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (9 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (9 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (9 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_10 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (10 * 65536 + x.val) = some (SubwordStorePlace.placed (10 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (10 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (10 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (10 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (10 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_11 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (11 * 65536 + x.val) = some (SubwordStorePlace.placed (11 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (11 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (11 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (11 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (11 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_12 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (12 * 65536 + x.val) = some (SubwordStorePlace.placed (12 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (12 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (12 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (12 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (12 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_13 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (13 * 65536 + x.val) = some (SubwordStorePlace.placed (13 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (13 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (13 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (13 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (13 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_14 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (14 * 65536 + x.val) = some (SubwordStorePlace.placed (14 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (14 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (14 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (14 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (14 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_15 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (15 * 65536 + x.val) = some (SubwordStorePlace.placed (15 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (15 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (15 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (15 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (15 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_16 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (16 * 65536 + x.val) = some (SubwordStorePlace.placed (16 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (16 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (16 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (16 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (16 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_17 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (17 * 65536 + x.val) = some (SubwordStorePlace.placed (17 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (17 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (17 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (17 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (17 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_18 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (18 * 65536 + x.val) = some (SubwordStorePlace.placed (18 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (18 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (18 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (18 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (18 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_19 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (19 * 65536 + x.val) = some (SubwordStorePlace.placed (19 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (19 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (19 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (19 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (19 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_20 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (20 * 65536 + x.val) = some (SubwordStorePlace.placed (20 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (20 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (20 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (20 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (20 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_21 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (21 * 65536 + x.val) = some (SubwordStorePlace.placed (21 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (21 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (21 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (21 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (21 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_22 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (22 * 65536 + x.val) = some (SubwordStorePlace.placed (22 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (22 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (22 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (22 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (22 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_23 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (23 * 65536 + x.val) = some (SubwordStorePlace.placed (23 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (23 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (23 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (23 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (23 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_24 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (24 * 65536 + x.val) = some (SubwordStorePlace.placed (24 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (24 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (24 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (24 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (24 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_25 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (25 * 65536 + x.val) = some (SubwordStorePlace.placed (25 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (25 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (25 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (25 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (25 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_26 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (26 * 65536 + x.val) = some (SubwordStorePlace.placed (26 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (26 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (26 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (26 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (26 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_27 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (27 * 65536 + x.val) = some (SubwordStorePlace.placed (27 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (27 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (27 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (27 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (27 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_28 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (28 * 65536 + x.val) = some (SubwordStorePlace.placed (28 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (28 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (28 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (28 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (28 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_29 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (29 * 65536 + x.val) = some (SubwordStorePlace.placed (29 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (29 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (29 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (29 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (29 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_30 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (30 * 65536 + x.val) = some (SubwordStorePlace.placed (30 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (30 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (30 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (30 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (30 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_group_31 (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (31 * 65536 + x.val) = some (SubwordStorePlace.placed (31 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (31 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (31 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (31 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordStorePlace.data.columns[1].blocks.toList (31 * 65536 + x.val) = _
  rw [place_blocks]
  rw [block_skip _ _ _ _ place_length_0 (by omega)]
  rw [block_skip _ _ _ _ place_length_1 (by omega)]
  rw [block_skip _ _ _ _ place_length_2 (by omega)]
  rw [block_skip _ _ _ _ place_length_3 (by omega)]
  rw [block_skip _ _ _ _ place_length_4 (by omega)]
  rw [block_skip _ _ _ _ place_length_5 (by omega)]
  rw [block_skip _ _ _ _ place_length_6 (by omega)]
  rw [block_skip _ _ _ _ place_length_7 (by omega)]
  rw [block_head _ _ _ _ place_length_8 (by omega)]
  rw [affine_zero_get 1572864 0 _ (by omega)]
  unfold SubwordStorePlace.placed
  rw [limb, offset, funct3]
  norm_num

private theorem place_grid (group : Fin 32) (x : Fin 65536) :
    NativeSubwordStorePlace.data.columns[1].get? (group.val * 65536 + x.val) =
      some (SubwordStorePlace.placed (group.val * 65536 + x.val)) := by
  fin_cases group
  · exact place_group_0 x
  · exact place_group_1 x
  · exact place_group_2 x
  · exact place_group_3 x
  · exact place_group_4 x
  · exact place_group_5 x
  · exact place_group_6 x
  · exact place_group_7 x
  · exact place_group_8 x
  · exact place_group_9 x
  · exact place_group_10 x
  · exact place_group_11 x
  · exact place_group_12 x
  · exact place_group_13 x
  · exact place_group_14 x
  · exact place_group_15 x
  · exact place_group_16 x
  · exact place_group_17 x
  · exact place_group_18 x
  · exact place_group_19 x
  · exact place_group_20 x
  · exact place_group_21 x
  · exact place_group_22 x
  · exact place_group_23 x
  · exact place_group_24 x
  · exact place_group_25 x
  · exact place_group_26 x
  · exact place_group_27 x
  · exact place_group_28 x
  · exact place_group_29 x
  · exact place_group_30 x
  · exact place_group_31 x

/-- All written-value placement outputs in the actual native literal columns. -/
theorem store_place_output (i : Fin 2097152) :
    NativeSubwordStorePlace.data.columns[1].get? i.val = some (SubwordStorePlace.placed i.val) := by
  have bound := i.isLt
  have group : i.val / 65536 < 32 := by omega
  have same : (i.val / 65536) * 65536 + i.val % 65536 = i.val := by omega
  simpa only [same] using place_grid ⟨i.val / 65536, group⟩
    ⟨i.val % 65536, Nat.mod_lt _ (by decide)⟩

/-- The placed byte or halfword always fits a canonical 16-bit limb. -/
theorem store_place_bounds (key : Nat) : SubwordStorePlace.placed key < 65536 := by
  have limb : key % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have lowByte : key % 65536 % 256 < 256 := Nat.mod_lt _ (by decide)
  unfold SubwordStorePlace.placed
  dsimp only
  split_ifs <;> omega

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

/-- Complete literal native rows, including the unused zero output and native tag. -/
theorem native_store_place_rows (i : Fin 2097152) :
    NativeSubwordStorePlace.data.rowNat i = (SubwordStorePlace.row i).push 55 := by
  have key : NativeSubwordStorePlace.data.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 2097152 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 0 1 i.val i.isLt
  have unused : NativeSubwordStorePlace.data.columns[2].get? i.val = some 0 := by
    change (⟨#[.affine 2097152 0 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 0 0 i.val i.isLt
  have tag : NativeSubwordStorePlace.data.columns[3].get? i.val = some 55 := by
    change (⟨#[.affine 2097152 55 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 55 0 i.val i.isLt
  have output := store_place_output i
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat, key, unused, tag, output, SubwordStorePlace.row]

/-- Original Clean lookup membership is exactly the literal native tagged relation. -/
theorem store_place_lookup (query : Vector (ZMod mersenne31Modulus) 3) :
    SubwordStorePlace.table.Contains #[] query ↔ ∃ i : Fin 2097152,
      query.push 55 = NativeSubwordStorePlace.data.row i := by
  change (∃ i : Fin 2097152, query = (SubwordStorePlace.row i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [TableData.row, native_store_place_rows, Vector.map_push]⟩
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    apply Vector.ext
    intro lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [TableData.row, native_store_place_rows, Vector.map_push,
      Vector.getElem_push, bound] using selected

/-- Native lookup derives the canonical key, exact placement, zero output and bound. -/
theorem store_place_values {key placed unused : ZMod mersenne31Modulus}
    (member : SubwordStorePlace.table.Contains #[] #v[key, placed, unused]) :
    key.val < 2097152 ∧ placed = (SubwordStorePlace.placed key.val : Nat) ∧
      unused = 0 ∧ placed.val < 65536 := by
  change ∃ i : Fin 2097152, #v[key, placed, unused] = (SubwordStorePlace.row i).map Nat.cast at member
  obtain ⟨i, same⟩ := member
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [SubwordStorePlace.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[0]) same
  have value : key.val = i.val := by
    rw [head, ZMod.val_natCast_of_lt (by have := i.isLt; unfold mersenne31Modulus; omega)]
  have placedEq : placed = (SubwordStorePlace.placed key.val : Nat) := by
    rw [value]
    simpa [SubwordStorePlace.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[1]) same
  have unusedEq : unused = 0 := by
    simpa [SubwordStorePlace.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[2]) same
  have bounded := store_place_bounds key.val
  have fieldLarge : 65536 < mersenne31Modulus := by decide
  refine ⟨by rw [value]; exact i.isLt, placedEq, unusedEq, ?_⟩
  rw [placedEq, ZMod.val_natCast_of_lt (lt_trans bounded fieldLarge)]
  exact bounded

end Airbender.SubwordMemory.StorePlaceProofs
