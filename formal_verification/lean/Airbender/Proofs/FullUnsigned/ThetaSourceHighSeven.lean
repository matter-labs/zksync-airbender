import Airbender.Proofs.FullUnsigned.SourceBlockGroupChecks
import Airbender.Proofs.FullUnsigned.SourceScaledChunks
import Airbender.Proofs.FullUnsigned.SourceBlockWindows
import Airbender.Proofs.FullUnsigned.ThetaSourceLowZero
import Airbender.Proofs.Keccak.SplitThetaFragmentValues

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn : Column := (SourceCaptureTheta.columns[4]?).getD ⟨#[]⟩
private noncomputable def window : List Block := (sourceColumn.blocks.toList.drop 132).take 516
private noncomputable def binding : SourceBank.ColumnBinding :=
  (SourceCaptureTheta.columnBindings[4]'(by change 4 < 9; decide +kernel)).1
private def expected (index : Nat) : Nat := (index / 512) ^^^ (index / 2 % 128)
private theorem prefix_length : ((sourceColumn.blocks.toList.take 132).map Block.length).sum = 524288 := by low_source_kernel_rfl
private theorem window_length : (window.map Block.length).sum = 65536 := by low_source_kernel_rfl

private noncomputable def group0 : List Block := [137, 137, 138, 138, 139, 139, 140, 140].map binding.blocks
private theorem group0_length : (group0.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group0_checked : checkBlockRows expected 0 group0 = true := by decide +kernel

private noncomputable def group1 : List Block := [141, 141, 142, 142, 143, 143, 144, 144].map binding.blocks
private theorem group1_length : (group1.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group1_checked : checkBlockRows expected 2048 group1 = true := by decide +kernel

private noncomputable def group2 : List Block := [145, 145, 146, 146, 147, 147, 148, 148].map binding.blocks
private theorem group2_length : (group2.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group2_checked : checkBlockRows expected 4096 group2 = true := by decide +kernel

private noncomputable def group3 : List Block := [149, 149, 150, 150, 151, 151, 152, 152].map binding.blocks
private theorem group3_length : (group3.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group3_checked : checkBlockRows expected 6144 group3 = true := by decide +kernel

private noncomputable def group4 : List Block := [153, 153, 154, 154, 155, 155, 156, 156].map binding.blocks
private theorem group4_length : (group4.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group4_checked : checkBlockRows expected 8192 group4 = true := by decide +kernel

private noncomputable def group5 : List Block := [157, 157, 158, 158, 159, 159, 160, 160].map binding.blocks
private theorem group5_length : (group5.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group5_checked : checkBlockRows expected 10240 group5 = true := by decide +kernel

private noncomputable def group6 : List Block := [161, 161, 162, 162, 163, 163, 164, 164].map binding.blocks
private theorem group6_length : (group6.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group6_checked : checkBlockRows expected 12288 group6 = true := by decide +kernel

private noncomputable def group7 : List Block := [165, 165, 166, 166, 167, 167, 168, 168].map binding.blocks
private theorem group7_length : (group7.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group7_checked : checkBlockRows expected 14336 group7 = true := by decide +kernel

private noncomputable def group8 : List Block := [169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188].map binding.blocks
private theorem group8_length : (group8.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group8_checked : checkBlockRows expected 16384 group8 = true := by decide +kernel

private noncomputable def group9 : List Block := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208].map binding.blocks
private theorem group9_length : (group9.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group9_checked : checkBlockRows expected 18432 group9 = true := by decide +kernel

private noncomputable def group10 : List Block := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278].map binding.blocks
private theorem group10_length : (group10.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group10_checked : checkBlockRows expected 20480 group10 = true := by decide +kernel

private noncomputable def group11 : List Block := [279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314].map binding.blocks
private theorem group11_length : (group11.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group11_checked : checkBlockRows expected 22528 group11 = true := by decide +kernel

private noncomputable def group12 : List Block := [315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326].map binding.blocks
private theorem group12_length : (group12.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group12_checked : checkBlockRows expected 24576 group12 = true := by decide +kernel

private noncomputable def group13 : List Block := [327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338].map binding.blocks
private theorem group13_length : (group13.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group13_checked : checkBlockRows expected 26624 group13 = true := by decide +kernel

private noncomputable def group14 : List Block := [339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350].map binding.blocks
private theorem group14_length : (group14.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group14_checked : checkBlockRows expected 28672 group14 = true := by decide +kernel

private noncomputable def group15 : List Block := [351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362].map binding.blocks
private theorem group15_length : (group15.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group15_checked : checkBlockRows expected 30720 group15 = true := by decide +kernel

private noncomputable def group16 : List Block := [363, 137, 364, 365, 138, 366, 367, 139, 368, 369, 140, 370].map binding.blocks
private theorem group16_length : (group16.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group16_checked : checkBlockRows expected 32768 group16 = true := by decide +kernel

private noncomputable def group17 : List Block := [371, 141, 372, 373, 142, 374, 375, 143, 376, 377, 144, 378].map binding.blocks
private theorem group17_length : (group17.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group17_checked : checkBlockRows expected 34816 group17 = true := by decide +kernel

private noncomputable def group18 : List Block := [379, 145, 380, 381, 146, 382, 383, 147, 384, 385, 148, 386].map binding.blocks
private theorem group18_length : (group18.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group18_checked : checkBlockRows expected 36864 group18 = true := by decide +kernel

private noncomputable def group19 : List Block := [387, 149, 388, 389, 150, 390, 391, 151, 392, 393, 152, 394].map binding.blocks
private theorem group19_length : (group19.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group19_checked : checkBlockRows expected 38912 group19 = true := by decide +kernel

private noncomputable def group20 : List Block := [395, 396, 397, 398, 153, 399, 400, 401, 402, 403, 404, 405, 406, 154, 407, 408, 409, 410, 411, 412, 413, 414, 155, 415, 416, 417, 418, 419, 420, 421, 422, 156, 423, 424, 425, 426].map binding.blocks
private theorem group20_length : (group20.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group20_checked : checkBlockRows expected 40960 group20 = true := by decide +kernel

private noncomputable def group21 : List Block := [427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 157, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 158, 460, 461, 462, 463, 464, 465, 466, 467, 468, 159, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 160, 485, 486, 487, 488, 489, 490, 491, 492].map binding.blocks
private theorem group21_length : (group21.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group21_checked : checkBlockRows expected 43008 group21 = true := by decide +kernel

private noncomputable def group22 : List Block := [493, 494, 161, 495, 496, 497, 498, 162, 499, 500, 501, 502, 163, 503, 504, 505, 506, 164, 507, 508].map binding.blocks
private theorem group22_length : (group22.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group22_checked : checkBlockRows expected 45056 group22 = true := by decide +kernel

private noncomputable def group23 : List Block := [509, 510, 165, 511, 512, 513, 514, 166, 515, 516, 517, 518, 167, 519, 520, 521, 522, 168, 523, 524].map binding.blocks
private theorem group23_length : (group23.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group23_checked : checkBlockRows expected 47104 group23 = true := by decide +kernel

private noncomputable def group24 : List Block := [171, 171, 176, 176, 181, 181, 186, 186].map binding.blocks
private theorem group24_length : (group24.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group24_checked : checkBlockRows expected 49152 group24 = true := by decide +kernel

private noncomputable def group25 : List Block := [191, 191, 196, 196, 201, 201, 206, 206].map binding.blocks
private theorem group25_length : (group25.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group25_checked : checkBlockRows expected 51200 group25 = true := by decide +kernel

private noncomputable def group26 : List Block := [217, 217, 234, 234, 244, 244, 262, 262].map binding.blocks
private theorem group26_length : (group26.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group26_checked : checkBlockRows expected 53248 group26 = true := by decide +kernel

private noncomputable def group27 : List Block := [283, 283, 292, 292, 301, 301, 310, 310].map binding.blocks
private theorem group27_length : (group27.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group27_checked : checkBlockRows expected 55296 group27 = true := by decide +kernel

private noncomputable def group28 : List Block := [316, 316, 319, 319, 322, 322, 325, 325].map binding.blocks
private theorem group28_length : (group28.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group28_checked : checkBlockRows expected 57344 group28 = true := by decide +kernel

private noncomputable def group29 : List Block := [328, 328, 331, 331, 334, 334, 337, 337].map binding.blocks
private theorem group29_length : (group29.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group29_checked : checkBlockRows expected 59392 group29 = true := by decide +kernel

private noncomputable def group30 : List Block := [340, 340, 343, 343, 346, 346, 349, 349].map binding.blocks
private theorem group30_length : (group30.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group30_checked : checkBlockRows expected 61440 group30 = true := by decide +kernel

private noncomputable def group31 : List Block := [352, 352, 355, 355, 358, 358, 361, 361].map binding.blocks
private theorem group31_length : (group31.map Block.length).sum = 2048 := by low_source_kernel_rfl
private theorem group31_checked : checkBlockRows expected 63488 group31 = true := by decide +kernel

private theorem window_groups : window = group0 ++ group1 ++ group2 ++ group3 ++ group4 ++ group5 ++ group6 ++ group7 ++ group8 ++ group9 ++ group10 ++ group11 ++ group12 ++ group13 ++ group14 ++ group15 ++ group16 ++ group17 ++ group18 ++ group19 ++ group20 ++ group21 ++ group22 ++ group23 ++ group24 ++ group25 ++ group26 ++ group27 ++ group28 ++ group29 ++ group30 ++ group31 := by low_source_kernel_rfl

private theorem window_checked : checkBlockRows expected 0 window = true := by
  rw [window_groups]
  simp only [List.append_assoc]
  rw [checkBlockRows_append, group0_checked, Bool.true_and, group0_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group1_checked, Bool.true_and, group1_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group2_checked, Bool.true_and, group2_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group3_checked, Bool.true_and, group3_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group4_checked, Bool.true_and, group4_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group5_checked, Bool.true_and, group5_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group6_checked, Bool.true_and, group6_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group7_checked, Bool.true_and, group7_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group8_checked, Bool.true_and, group8_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group9_checked, Bool.true_and, group9_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group10_checked, Bool.true_and, group10_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group11_checked, Bool.true_and, group11_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group12_checked, Bool.true_and, group12_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group13_checked, Bool.true_and, group13_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group14_checked, Bool.true_and, group14_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group15_checked, Bool.true_and, group15_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group16_checked, Bool.true_and, group16_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group17_checked, Bool.true_and, group17_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group18_checked, Bool.true_and, group18_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group19_checked, Bool.true_and, group19_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group20_checked, Bool.true_and, group20_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group21_checked, Bool.true_and, group21_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group22_checked, Bool.true_and, group22_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group23_checked, Bool.true_and, group23_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group24_checked, Bool.true_and, group24_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group25_checked, Bool.true_and, group25_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group26_checked, Bool.true_and, group26_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group27_checked, Bool.true_and, group27_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group28_checked, Bool.true_and, group28_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group29_checked, Bool.true_and, group29_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group30_checked, Bool.true_and, group30_length]
  norm_num only [Nat.reduceAdd]
  exact group31_checked

/-- Bounded kernel checks prove the exact source overflow for shift seven. -/
theorem source_split_high_seven_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (524288 + index.val) =
      some ((index.val / 512) ^^^ (index.val / 2 % 128)) := by
  have selected := getFromBlocks_window sourceColumn.blocks.toList 132 516 524288 index.val
    prefix_length (by change index.val < (window.map Block.length).sum; rw [window_length]; exact index.isLt)
  change getFromBlocks sourceColumn.blocks.toList (524288 + index.val) = _
  rw [selected]
  change getFromBlocks window index.val = _
  simpa only [Nat.zero_add, expected] using checkBlockRows_sound expected window 0 index.val window_checked
    (by rw [window_length]; exact index.isLt)

/-- The stored source overflow equals its complete native value. -/
theorem source_split_high_seven_match (index : Fin 65536) :
    (((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (524288 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[4]).value (458752 + index.val) := by
  rw [source_split_high_seven_get, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_high_value
    ⟨458752 + index.val, by change 458752 + index.val < 524288; have bound := index.isLt; omega⟩
  have shift : (458752 + index.val) / 65536 = 7 := by omega
  have high : (458752 + index.val) / 256 % 256 = index.val / 256 % 256 := by omega
  have low : (458752 + index.val) % 256 = index.val % 256 := by omega
  rw [shift, high, low] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) / 2 at native
  rw [native]
  have split := Nat.xor_div_two_pow (a := index.val / 256 % 256) (b := index.val % 256) (n := 1)
  change _ / 2 = _ at split
  have hdiv : index.val / 256 % 256 / 2 = index.val / 512 := by omega
  have ldiv : index.val % 256 / 2 = index.val / 2 % 128 := by omega
  simpa only [hdiv, ldiv] using split.symm

end Airbender.Setup.SourceCaptureThetaProofs
