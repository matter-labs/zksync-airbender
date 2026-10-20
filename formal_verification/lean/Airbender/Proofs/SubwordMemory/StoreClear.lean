import Airbender.Review.Helpers.Tables.NativeSubwordStoreClearData
import Airbender.Review.Helpers.Tables.SubwordStoreClear
import Airbender.Proofs.SubwordMemory.LoadGetters
import Airbender.Proofs.Mersenne31

namespace Airbender.SubwordMemory.StoreClearProofs
open Setup Verification Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

private theorem clear_blocks : NativeSubwordStoreClear.data.columns[1].blocks.toList =
    [.periodic 256 256 (Array.replicate 256 0), .periodic 256 0 (Array.range 256),
     .periodic 256 256 (Array.replicate 256 0), .periodic 256 0 (Array.range 256),
     .affine 1835008 0 0] := rfl

-- The periodic upper-byte getter is adapted from pinned v3 ImportedStoreClear.
private theorem clear_upper (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 256 (Array.replicate 256 0)) n =
      some (256 * (n / 256)) := by
  have row := Setup.Proofs.periodic_get (Array.replicate 256 0) 256 256 n (by simp)
    (by simpa only [Array.size_replicate] using bound)
  simpa using row

private theorem clear_length_0 : (.periodic 256 256 (Array.replicate 256 0) : Block).length = 65536 := by norm_num only [Block.length, Array.size_replicate, Array.size_range]

private theorem clear_length_1 : (.periodic 256 0 (Array.range 256) : Block).length = 65536 := by norm_num only [Block.length, Array.size_replicate, Array.size_range]

private theorem clear_length_2 : (.periodic 256 256 (Array.replicate 256 0) : Block).length = 65536 := by norm_num only [Block.length, Array.size_replicate, Array.size_range]

private theorem clear_length_3 : (.periodic 256 0 (Array.range 256) : Block).length = 65536 := by norm_num only [Block.length, Array.size_replicate, Array.size_range]

private theorem clear_length_4 : (.affine 1835008 0 0 : Block).length = 1835008 := by norm_num only [Block.length, Array.size_replicate, Array.size_range]

private theorem clear_group_0 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (0 * 65536 + x.val) = some (SubwordStoreClear.cleared (0 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (0 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (0 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (0 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (0 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_head _ _ _ _ clear_length_0 (by omega)]
  rw [clear_upper _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_1 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (1 * 65536 + x.val) = some (SubwordStoreClear.cleared (1 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (1 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (1 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (1 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (1 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_head _ _ _ _ clear_length_1 (by omega)]
  rw [range_get _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_2 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (2 * 65536 + x.val) = some (SubwordStoreClear.cleared (2 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (2 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (2 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (2 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (2 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_head _ _ _ _ clear_length_2 (by omega)]
  rw [clear_upper _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem clear_group_3 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (3 * 65536 + x.val) = some (SubwordStoreClear.cleared (3 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (3 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (3 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (3 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (3 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_head _ _ _ _ clear_length_3 (by omega)]
  rw [range_get _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem clear_group_4 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (4 * 65536 + x.val) = some (SubwordStoreClear.cleared (4 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (4 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (4 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (4 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (4 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_5 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (5 * 65536 + x.val) = some (SubwordStoreClear.cleared (5 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (5 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (5 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (5 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (5 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_6 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (6 * 65536 + x.val) = some (SubwordStoreClear.cleared (6 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (6 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (6 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (6 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (6 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_7 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (7 * 65536 + x.val) = some (SubwordStoreClear.cleared (7 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (7 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (7 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (7 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (7 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_8 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (8 * 65536 + x.val) = some (SubwordStoreClear.cleared (8 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (8 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (8 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (8 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (8 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_9 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (9 * 65536 + x.val) = some (SubwordStoreClear.cleared (9 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (9 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (9 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (9 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (9 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_10 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (10 * 65536 + x.val) = some (SubwordStoreClear.cleared (10 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (10 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (10 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (10 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (10 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_11 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (11 * 65536 + x.val) = some (SubwordStoreClear.cleared (11 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (11 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (11 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (11 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (11 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_12 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (12 * 65536 + x.val) = some (SubwordStoreClear.cleared (12 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (12 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (12 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (12 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (12 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_13 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (13 * 65536 + x.val) = some (SubwordStoreClear.cleared (13 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (13 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (13 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (13 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (13 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_14 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (14 * 65536 + x.val) = some (SubwordStoreClear.cleared (14 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (14 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (14 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (14 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (14 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_15 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (15 * 65536 + x.val) = some (SubwordStoreClear.cleared (15 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (15 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (15 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (15 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (15 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_16 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (16 * 65536 + x.val) = some (SubwordStoreClear.cleared (16 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (16 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (16 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (16 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (16 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_17 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (17 * 65536 + x.val) = some (SubwordStoreClear.cleared (17 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (17 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (17 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (17 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (17 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_18 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (18 * 65536 + x.val) = some (SubwordStoreClear.cleared (18 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (18 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (18 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (18 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (18 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_19 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (19 * 65536 + x.val) = some (SubwordStoreClear.cleared (19 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (19 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (19 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (19 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (19 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_20 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (20 * 65536 + x.val) = some (SubwordStoreClear.cleared (20 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (20 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (20 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (20 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (20 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_21 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (21 * 65536 + x.val) = some (SubwordStoreClear.cleared (21 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (21 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (21 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (21 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (21 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_22 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (22 * 65536 + x.val) = some (SubwordStoreClear.cleared (22 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (22 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (22 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (22 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (22 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_23 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (23 * 65536 + x.val) = some (SubwordStoreClear.cleared (23 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (23 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (23 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (23 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (23 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_24 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (24 * 65536 + x.val) = some (SubwordStoreClear.cleared (24 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (24 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (24 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (24 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (24 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_25 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (25 * 65536 + x.val) = some (SubwordStoreClear.cleared (25 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (25 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (25 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (25 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (25 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_26 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (26 * 65536 + x.val) = some (SubwordStoreClear.cleared (26 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (26 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (26 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (26 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (26 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_27 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (27 * 65536 + x.val) = some (SubwordStoreClear.cleared (27 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (27 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (27 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (27 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (27 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_28 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (28 * 65536 + x.val) = some (SubwordStoreClear.cleared (28 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (28 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (28 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (28 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (28 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_29 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (29 * 65536 + x.val) = some (SubwordStoreClear.cleared (29 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (29 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (29 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (29 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (29 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_30 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (30 * 65536 + x.val) = some (SubwordStoreClear.cleared (30 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (30 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (30 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (30 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (30 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_group_31 (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (31 * 65536 + x.val) = some (SubwordStoreClear.cleared (31 * 65536 + x.val)) := by
  have hx := x.isLt
  have limb : (31 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (31 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (31 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordStoreClear.data.columns[1].blocks.toList (31 * 65536 + x.val) = _
  rw [clear_blocks]
  rw [block_skip _ _ _ _ clear_length_0 (by omega)]
  rw [block_skip _ _ _ _ clear_length_1 (by omega)]
  rw [block_skip _ _ _ _ clear_length_2 (by omega)]
  rw [block_skip _ _ _ _ clear_length_3 (by omega)]
  rw [block_head _ _ _ _ clear_length_4 (by omega)]
  rw [affine_zero_get 1835008 0 _ (by omega)]
  unfold SubwordStoreClear.cleared
  rw [limb, offset, funct3]
  norm_num

private theorem clear_grid (group : Fin 32) (x : Fin 65536) :
    NativeSubwordStoreClear.data.columns[1].get? (group.val * 65536 + x.val) =
      some (SubwordStoreClear.cleared (group.val * 65536 + x.val)) := by
  fin_cases group
  · exact clear_group_0 x
  · exact clear_group_1 x
  · exact clear_group_2 x
  · exact clear_group_3 x
  · exact clear_group_4 x
  · exact clear_group_5 x
  · exact clear_group_6 x
  · exact clear_group_7 x
  · exact clear_group_8 x
  · exact clear_group_9 x
  · exact clear_group_10 x
  · exact clear_group_11 x
  · exact clear_group_12 x
  · exact clear_group_13 x
  · exact clear_group_14 x
  · exact clear_group_15 x
  · exact clear_group_16 x
  · exact clear_group_17 x
  · exact clear_group_18 x
  · exact clear_group_19 x
  · exact clear_group_20 x
  · exact clear_group_21 x
  · exact clear_group_22 x
  · exact clear_group_23 x
  · exact clear_group_24 x
  · exact clear_group_25 x
  · exact clear_group_26 x
  · exact clear_group_27 x
  · exact clear_group_28 x
  · exact clear_group_29 x
  · exact clear_group_30 x
  · exact clear_group_31 x

/-- All original-RAM-limb clearing outputs in the actual native literal columns. -/
theorem store_clear_output (i : Fin 2097152) :
    NativeSubwordStoreClear.data.columns[1].get? i.val = some (SubwordStoreClear.cleared i.val) := by
  have bound := i.isLt
  have group : i.val / 65536 < 32 := by omega
  have same : (i.val / 65536) * 65536 + i.val % 65536 = i.val := by omega
  simpa only [same] using clear_grid ⟨i.val / 65536, group⟩
    ⟨i.val % 65536, Nat.mod_lt _ (by decide)⟩

/-- The retained original byte always fits a canonical 16-bit limb. -/
theorem store_clear_bounds (key : Nat) : SubwordStoreClear.cleared key < 65536 := by
  have limb : key % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have lowByte : key % 65536 % 256 < 256 := Nat.mod_lt _ (by decide)
  have highByte : key % 65536 / 256 < 256 := by omega
  unfold SubwordStoreClear.cleared
  dsimp only
  split_ifs <;> omega

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

/-- Complete literal native rows, including the unused zero output and native tag. -/
theorem native_store_clear_rows (i : Fin 2097152) :
    NativeSubwordStoreClear.data.rowNat i = (SubwordStoreClear.row i).push 54 := by
  have key : NativeSubwordStoreClear.data.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 2097152 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 0 1 i.val i.isLt
  have unused : NativeSubwordStoreClear.data.columns[2].get? i.val = some 0 := by
    change (⟨#[.affine 2097152 0 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 0 0 i.val i.isLt
  have tag : NativeSubwordStoreClear.data.columns[3].get? i.val = some 54 := by
    change (⟨#[.affine 2097152 54 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 2097152 54 0 i.val i.isLt
  have output := store_clear_output i
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat, key, unused, tag, output, SubwordStoreClear.row]

/-- Original Clean lookup membership is exactly the literal native tagged relation. -/
theorem store_clear_lookup (query : Vector (ZMod mersenne31Modulus) 3) :
    SubwordStoreClear.table.Contains #[] query ↔ ∃ i : Fin 2097152,
      query.push 54 = NativeSubwordStoreClear.data.row i := by
  change (∃ i : Fin 2097152, query = (SubwordStoreClear.row i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [TableData.row, native_store_clear_rows, Vector.map_push]⟩
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    apply Vector.ext
    intro lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [TableData.row, native_store_clear_rows, Vector.map_push,
      Vector.getElem_push, bound] using selected

/-- Native lookup derives the canonical key, exact clearing, zero output and bound. -/
theorem store_clear_values {key cleared unused : ZMod mersenne31Modulus}
    (member : SubwordStoreClear.table.Contains #[] #v[key, cleared, unused]) :
    key.val < 2097152 ∧ cleared = (SubwordStoreClear.cleared key.val : Nat) ∧
      unused = 0 ∧ cleared.val < 65536 := by
  change ∃ i : Fin 2097152, #v[key, cleared, unused] = (SubwordStoreClear.row i).map Nat.cast at member
  obtain ⟨i, same⟩ := member
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [SubwordStoreClear.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[0]) same
  have value : key.val = i.val := by
    rw [head, ZMod.val_natCast_of_lt (by have := i.isLt; unfold mersenne31Modulus; omega)]
  have clearedEq : cleared = (SubwordStoreClear.cleared key.val : Nat) := by
    rw [value]
    simpa [SubwordStoreClear.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[1]) same
  have unusedEq : unused = 0 := by
    simpa [SubwordStoreClear.row] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[2]) same
  have bounded := store_clear_bounds key.val
  have fieldLarge : 65536 < mersenne31Modulus := by decide
  refine ⟨by rw [value]; exact i.isLt, clearedEq, unusedEq, ?_⟩
  rw [clearedEq, ZMod.val_natCast_of_lt (lt_trans bounded fieldLarge)]
  exact bounded

end Airbender.SubwordMemory.StoreClearProofs
