import Airbender.Proofs.SubwordMemory.LoadGetters

namespace Airbender.SubwordMemory.LoadProofs
open Setup Verification
set_option autoImplicit false

private theorem low_length_0 : (.periodic 256 0 lowSignValues : Block).length = 65536 := by norm_num only [Block.length, lowSignValues_size]

private theorem low_length_1 : (.periodic 128 1 (Array.replicate 256 0) : Block).length = 32768 := by norm_num only [Block.length, Array.size_replicate]

private theorem low_length_2 : (.periodic 128 1 (Array.replicate 256 65408) : Block).length = 32768 := by norm_num only [Block.length, Array.size_replicate]

private theorem low_length_3 : (.periodic 256 0 lowSignValues : Block).length = 65536 := by norm_num only [Block.length, lowSignValues_size]

private theorem low_length_4 : (.periodic 128 1 (Array.replicate 256 0) : Block).length = 32768 := by norm_num only [Block.length, Array.size_replicate]

private theorem low_length_5 : (.periodic 128 1 (Array.replicate 256 65408) : Block).length = 32768 := by norm_num only [Block.length, Array.size_replicate]

private theorem low_length_6 : (.affine 65536 0 1 : Block).length = 65536 := by norm_num only [Block.length]

private theorem low_length_7 : (.affine 65537 0 0 : Block).length = 65537 := by norm_num only [Block.length]

private theorem low_length_8 : (.affine 65535 1 1 : Block).length = 65535 := by norm_num only [Block.length]

private theorem low_length_9 : (.affine 589825 0 0 : Block).length = 589825 := by norm_num only [Block.length]

private theorem low_length_10 : (.periodic 256 0 rotatedByteValues : Block).length = 65536 := by norm_num only [Block.length, rotatedByteValues_size]

private theorem low_length_11 : (.periodic 255 1 rotatedCarryValues : Block).length = 65280 := by norm_num only [Block.length, rotatedCarryValues_size]

private theorem low_length_12 : (.affine 255 255 0 : Block).length = 255 := by norm_num only [Block.length]

private theorem low_length_13 : (.periodic 256 0 (Array.range 256) : Block).length = 65536 := by norm_num only [Block.length, Array.size_range]

private theorem low_length_14 : (.periodic 256 1 (Array.replicate 256 0) : Block).length = 65536 := by norm_num only [Block.length, Array.size_replicate]

private theorem low_length_15 : (.affine 65536 0 1 : Block).length = 65536 := by norm_num only [Block.length]

private theorem low_length_16 : (.affine 65537 0 0 : Block).length = 65537 := by norm_num only [Block.length]

private theorem low_length_17 : (.affine 65535 1 1 : Block).length = 65535 := by norm_num only [Block.length]

private theorem low_length_18 : (.affine 589824 0 0 : Block).length = 589824 := by norm_num only [Block.length]

private theorem low_group_0 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (0 * 65536 + x.val) = some ((SubwordLoad.limbs (0 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (0 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (0 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (0 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (0 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_head _ _ _ _ low_length_0 (by omega)]
  rw [signed_low_get _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_1 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (1 * 65536 + x.val) = some ((SubwordLoad.limbs (1 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (1 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (1 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (1 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (1 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  by_cases h2 : x.val < 32768
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_head _ _ _ _ low_length_1 (by omega)]
    rw [repeated_get 128 0 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    omega
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_head _ _ _ _ low_length_2 (by omega)]
    rw [repeated_get 128 65408 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    split_ifs <;> omega

private theorem low_group_2 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (2 * 65536 + x.val) = some ((SubwordLoad.limbs (2 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (2 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (2 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (2 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (2 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_head _ _ _ _ low_length_3 (by omega)]
  rw [signed_low_get _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num
  split_ifs <;> omega

private theorem low_group_3 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (3 * 65536 + x.val) = some ((SubwordLoad.limbs (3 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (3 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (3 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (3 * 65536 + x.val) / 262144 % 8 = 0 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (3 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  by_cases h2 : x.val < 32768
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_head _ _ _ _ low_length_4 (by omega)]
    rw [repeated_get 128 0 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    split_ifs <;> omega
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_skip _ _ _ _ low_length_4 (by omega)]
    rw [block_head _ _ _ _ low_length_5 (by omega)]
    rw [repeated_get 128 65408 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    split_ifs <;> omega

private theorem low_group_4 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (4 * 65536 + x.val) = some ((SubwordLoad.limbs (4 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (4 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (4 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (4 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (4 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_head _ _ _ _ low_length_6 (by omega)]
  rw [affine_one_get 65536 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem low_group_5 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (5 * 65536 + x.val) = some ((SubwordLoad.limbs (5 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (5 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (5 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (5 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (5 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_head _ _ _ _ low_length_7 (by omega)]
  rw [affine_zero_get 65537 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_6 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (6 * 65536 + x.val) = some ((SubwordLoad.limbs (6 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (6 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (6 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (6 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (6 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  by_cases h2 : x.val < 1
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_skip _ _ _ _ low_length_4 (by omega)]
    rw [block_skip _ _ _ _ low_length_5 (by omega)]
    rw [block_skip _ _ _ _ low_length_6 (by omega)]
    rw [block_head _ _ _ _ low_length_7 (by omega)]
    rw [affine_zero_get 65537 0 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    omega
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_skip _ _ _ _ low_length_4 (by omega)]
    rw [block_skip _ _ _ _ low_length_5 (by omega)]
    rw [block_skip _ _ _ _ low_length_6 (by omega)]
    rw [block_skip _ _ _ _ low_length_7 (by omega)]
    rw [block_head _ _ _ _ low_length_8 (by omega)]
    rw [affine_one_get 65535 1 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    omega

private theorem low_group_7 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (7 * 65536 + x.val) = some ((SubwordLoad.limbs (7 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (7 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (7 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (7 * 65536 + x.val) / 262144 % 8 = 1 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (7 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_8 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (8 * 65536 + x.val) = some ((SubwordLoad.limbs (8 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (8 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (8 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (8 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (8 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_9 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (9 * 65536 + x.val) = some ((SubwordLoad.limbs (9 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (9 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (9 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (9 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (9 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_10 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (10 * 65536 + x.val) = some ((SubwordLoad.limbs (10 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (10 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (10 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (10 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (10 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_11 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (11 * 65536 + x.val) = some ((SubwordLoad.limbs (11 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (11 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (11 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (11 * 65536 + x.val) / 262144 % 8 = 2 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (11 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_12 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (12 * 65536 + x.val) = some ((SubwordLoad.limbs (12 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (12 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (12 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (12 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (12 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_13 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (13 * 65536 + x.val) = some ((SubwordLoad.limbs (13 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (13 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (13 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (13 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (13 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_14 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (14 * 65536 + x.val) = some ((SubwordLoad.limbs (14 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (14 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (14 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (14 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (14 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_15 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (15 * 65536 + x.val) = some ((SubwordLoad.limbs (15 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (15 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (15 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (15 * 65536 + x.val) / 262144 % 8 = 3 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (15 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_head _ _ _ _ low_length_9 (by omega)]
  rw [affine_zero_get 589825 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_16 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (16 * 65536 + x.val) = some ((SubwordLoad.limbs (16 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (16 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (16 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (16 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (16 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  by_cases h2 : x.val < 1
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_skip _ _ _ _ low_length_4 (by omega)]
    rw [block_skip _ _ _ _ low_length_5 (by omega)]
    rw [block_skip _ _ _ _ low_length_6 (by omega)]
    rw [block_skip _ _ _ _ low_length_7 (by omega)]
    rw [block_skip _ _ _ _ low_length_8 (by omega)]
    rw [block_head _ _ _ _ low_length_9 (by omega)]
    rw [affine_zero_get 589825 0 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    omega
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_skip _ _ _ _ low_length_4 (by omega)]
    rw [block_skip _ _ _ _ low_length_5 (by omega)]
    rw [block_skip _ _ _ _ low_length_6 (by omega)]
    rw [block_skip _ _ _ _ low_length_7 (by omega)]
    rw [block_skip _ _ _ _ low_length_8 (by omega)]
    rw [block_skip _ _ _ _ low_length_9 (by omega)]
    rw [block_head _ _ _ _ low_length_10 (by omega)]
    rw [rotated_byte_get _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    omega

private theorem low_group_17 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (17 * 65536 + x.val) = some ((SubwordLoad.limbs (17 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (17 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (17 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (17 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (17 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  by_cases h3 : x.val < 1
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_skip _ _ _ _ low_length_4 (by omega)]
    rw [block_skip _ _ _ _ low_length_5 (by omega)]
    rw [block_skip _ _ _ _ low_length_6 (by omega)]
    rw [block_skip _ _ _ _ low_length_7 (by omega)]
    rw [block_skip _ _ _ _ low_length_8 (by omega)]
    rw [block_skip _ _ _ _ low_length_9 (by omega)]
    rw [block_head _ _ _ _ low_length_10 (by omega)]
    rw [rotated_byte_get _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    omega
  · by_cases h2 : x.val < 65281
    · rw [block_skip _ _ _ _ low_length_0 (by omega)]
      rw [block_skip _ _ _ _ low_length_1 (by omega)]
      rw [block_skip _ _ _ _ low_length_2 (by omega)]
      rw [block_skip _ _ _ _ low_length_3 (by omega)]
      rw [block_skip _ _ _ _ low_length_4 (by omega)]
      rw [block_skip _ _ _ _ low_length_5 (by omega)]
      rw [block_skip _ _ _ _ low_length_6 (by omega)]
      rw [block_skip _ _ _ _ low_length_7 (by omega)]
      rw [block_skip _ _ _ _ low_length_8 (by omega)]
      rw [block_skip _ _ _ _ low_length_9 (by omega)]
      rw [block_skip _ _ _ _ low_length_10 (by omega)]
      rw [block_head _ _ _ _ low_length_11 (by omega)]
      rw [rotated_carry_get _ (by omega)]
      unfold SubwordLoad.limbs
      rw [limb, offset, funct3]
      norm_num
      omega
    · rw [block_skip _ _ _ _ low_length_0 (by omega)]
      rw [block_skip _ _ _ _ low_length_1 (by omega)]
      rw [block_skip _ _ _ _ low_length_2 (by omega)]
      rw [block_skip _ _ _ _ low_length_3 (by omega)]
      rw [block_skip _ _ _ _ low_length_4 (by omega)]
      rw [block_skip _ _ _ _ low_length_5 (by omega)]
      rw [block_skip _ _ _ _ low_length_6 (by omega)]
      rw [block_skip _ _ _ _ low_length_7 (by omega)]
      rw [block_skip _ _ _ _ low_length_8 (by omega)]
      rw [block_skip _ _ _ _ low_length_9 (by omega)]
      rw [block_skip _ _ _ _ low_length_10 (by omega)]
      rw [block_skip _ _ _ _ low_length_11 (by omega)]
      rw [block_head _ _ _ _ low_length_12 (by omega)]
      rw [affine_zero_get 255 255 _ (by omega)]
      unfold SubwordLoad.limbs
      rw [limb, offset, funct3]
      norm_num
      omega

private theorem low_group_18 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (18 * 65536 + x.val) = some ((SubwordLoad.limbs (18 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (18 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (18 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (18 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (18 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_head _ _ _ _ low_length_13 (by omega)]
  rw [range_get _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem low_group_19 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (19 * 65536 + x.val) = some ((SubwordLoad.limbs (19 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (19 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (19 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (19 * 65536 + x.val) / 262144 % 8 = 4 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (19 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_head _ _ _ _ low_length_14 (by omega)]
  rw [repeated_get 256 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem low_group_20 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (20 * 65536 + x.val) = some ((SubwordLoad.limbs (20 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (20 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (20 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (20 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (20 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_head _ _ _ _ low_length_15 (by omega)]
  rw [affine_one_get 65536 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num
  omega

private theorem low_group_21 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (21 * 65536 + x.val) = some ((SubwordLoad.limbs (21 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (21 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (21 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (21 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (21 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_head _ _ _ _ low_length_16 (by omega)]
  rw [affine_zero_get 65537 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_22 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (22 * 65536 + x.val) = some ((SubwordLoad.limbs (22 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (22 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (22 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (22 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (22 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  by_cases h2 : x.val < 1
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_skip _ _ _ _ low_length_4 (by omega)]
    rw [block_skip _ _ _ _ low_length_5 (by omega)]
    rw [block_skip _ _ _ _ low_length_6 (by omega)]
    rw [block_skip _ _ _ _ low_length_7 (by omega)]
    rw [block_skip _ _ _ _ low_length_8 (by omega)]
    rw [block_skip _ _ _ _ low_length_9 (by omega)]
    rw [block_skip _ _ _ _ low_length_10 (by omega)]
    rw [block_skip _ _ _ _ low_length_11 (by omega)]
    rw [block_skip _ _ _ _ low_length_12 (by omega)]
    rw [block_skip _ _ _ _ low_length_13 (by omega)]
    rw [block_skip _ _ _ _ low_length_14 (by omega)]
    rw [block_skip _ _ _ _ low_length_15 (by omega)]
    rw [block_head _ _ _ _ low_length_16 (by omega)]
    rw [affine_zero_get 65537 0 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    omega
  · rw [block_skip _ _ _ _ low_length_0 (by omega)]
    rw [block_skip _ _ _ _ low_length_1 (by omega)]
    rw [block_skip _ _ _ _ low_length_2 (by omega)]
    rw [block_skip _ _ _ _ low_length_3 (by omega)]
    rw [block_skip _ _ _ _ low_length_4 (by omega)]
    rw [block_skip _ _ _ _ low_length_5 (by omega)]
    rw [block_skip _ _ _ _ low_length_6 (by omega)]
    rw [block_skip _ _ _ _ low_length_7 (by omega)]
    rw [block_skip _ _ _ _ low_length_8 (by omega)]
    rw [block_skip _ _ _ _ low_length_9 (by omega)]
    rw [block_skip _ _ _ _ low_length_10 (by omega)]
    rw [block_skip _ _ _ _ low_length_11 (by omega)]
    rw [block_skip _ _ _ _ low_length_12 (by omega)]
    rw [block_skip _ _ _ _ low_length_13 (by omega)]
    rw [block_skip _ _ _ _ low_length_14 (by omega)]
    rw [block_skip _ _ _ _ low_length_15 (by omega)]
    rw [block_skip _ _ _ _ low_length_16 (by omega)]
    rw [block_head _ _ _ _ low_length_17 (by omega)]
    rw [affine_one_get 65535 1 _ (by omega)]
    unfold SubwordLoad.limbs
    rw [limb, offset, funct3]
    norm_num
    omega

private theorem low_group_23 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (23 * 65536 + x.val) = some ((SubwordLoad.limbs (23 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (23 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (23 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (23 * 65536 + x.val) / 262144 % 8 = 5 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (23 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_24 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (24 * 65536 + x.val) = some ((SubwordLoad.limbs (24 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (24 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (24 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (24 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (24 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_25 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (25 * 65536 + x.val) = some ((SubwordLoad.limbs (25 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (25 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (25 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (25 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (25 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_26 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (26 * 65536 + x.val) = some ((SubwordLoad.limbs (26 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (26 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (26 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (26 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (26 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_27 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (27 * 65536 + x.val) = some ((SubwordLoad.limbs (27 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (27 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (27 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (27 * 65536 + x.val) / 262144 % 8 = 6 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (27 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_28 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (28 * 65536 + x.val) = some ((SubwordLoad.limbs (28 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (28 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (28 * 65536 + x.val) / 65536 % 4 = 0 := by omega
  have funct3 : (28 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (28 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_29 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (29 * 65536 + x.val) = some ((SubwordLoad.limbs (29 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (29 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (29 * 65536 + x.val) / 65536 % 4 = 1 := by omega
  have funct3 : (29 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (29 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_30 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (30 * 65536 + x.val) = some ((SubwordLoad.limbs (30 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (30 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (30 * 65536 + x.val) / 65536 % 4 = 2 := by omega
  have funct3 : (30 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (30 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_group_31 (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (31 * 65536 + x.val) = some ((SubwordLoad.limbs (31 * 65536 + x.val)).1) := by
  have hx := x.isLt
  have limb : (31 * 65536 + x.val) % 65536 = x.val := by omega
  have offset : (31 * 65536 + x.val) / 65536 % 4 = 3 := by omega
  have funct3 : (31 * 65536 + x.val) / 262144 % 8 = 7 := by omega
  change getFromBlocks NativeSubwordLoad.data.columns[1].blocks.toList (31 * 65536 + x.val) = _
  rw [lowBlocks_shape]
  unfold lowBlocks
  rw [block_skip _ _ _ _ low_length_0 (by omega)]
  rw [block_skip _ _ _ _ low_length_1 (by omega)]
  rw [block_skip _ _ _ _ low_length_2 (by omega)]
  rw [block_skip _ _ _ _ low_length_3 (by omega)]
  rw [block_skip _ _ _ _ low_length_4 (by omega)]
  rw [block_skip _ _ _ _ low_length_5 (by omega)]
  rw [block_skip _ _ _ _ low_length_6 (by omega)]
  rw [block_skip _ _ _ _ low_length_7 (by omega)]
  rw [block_skip _ _ _ _ low_length_8 (by omega)]
  rw [block_skip _ _ _ _ low_length_9 (by omega)]
  rw [block_skip _ _ _ _ low_length_10 (by omega)]
  rw [block_skip _ _ _ _ low_length_11 (by omega)]
  rw [block_skip _ _ _ _ low_length_12 (by omega)]
  rw [block_skip _ _ _ _ low_length_13 (by omega)]
  rw [block_skip _ _ _ _ low_length_14 (by omega)]
  rw [block_skip _ _ _ _ low_length_15 (by omega)]
  rw [block_skip _ _ _ _ low_length_16 (by omega)]
  rw [block_skip _ _ _ _ low_length_17 (by omega)]
  rw [block_head _ _ _ _ low_length_18 (by omega)]
  rw [affine_zero_get 589824 0 _ (by omega)]
  unfold SubwordLoad.limbs
  rw [limb, offset, funct3]
  norm_num

private theorem low_grid (group : Fin 32) (x : Fin 65536) :
    NativeSubwordLoad.data.columns[1].get? (group.val * 65536 + x.val) =
      some ((SubwordLoad.limbs (group.val * 65536 + x.val)).1) := by
  fin_cases group
  · exact low_group_0 x
  · exact low_group_1 x
  · exact low_group_2 x
  · exact low_group_3 x
  · exact low_group_4 x
  · exact low_group_5 x
  · exact low_group_6 x
  · exact low_group_7 x
  · exact low_group_8 x
  · exact low_group_9 x
  · exact low_group_10 x
  · exact low_group_11 x
  · exact low_group_12 x
  · exact low_group_13 x
  · exact low_group_14 x
  · exact low_group_15 x
  · exact low_group_16 x
  · exact low_group_17 x
  · exact low_group_18 x
  · exact low_group_19 x
  · exact low_group_20 x
  · exact low_group_21 x
  · exact low_group_22 x
  · exact low_group_23 x
  · exact low_group_24 x
  · exact low_group_25 x
  · exact low_group_26 x
  · exact low_group_27 x
  · exact low_group_28 x
  · exact low_group_29 x
  · exact low_group_30 x
  · exact low_group_31 x

/-- Every actual native low output, including every unused and misaligned key. -/
theorem low_output (i : Fin 2097152) :
    NativeSubwordLoad.data.columns[1].get? i.val = some ((SubwordLoad.limbs i.val).1) := by
  let group : Fin 32 := ⟨i.val / 65536, by omega⟩
  let x : Fin 65536 := ⟨i.val % 65536, Nat.mod_lt _ (by decide)⟩
  have same : group.val * 65536 + x.val = i.val := by
    dsimp [group, x]
    omega
  simpa only [same] using low_grid group x

end Airbender.SubwordMemory.LoadProofs
