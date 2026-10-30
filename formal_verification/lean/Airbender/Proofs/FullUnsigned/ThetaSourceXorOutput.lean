import Airbender.Proofs.FullUnsigned.SourceBlockGroupChecks
import Airbender.Proofs.FullUnsigned.Source.Theta
import Airbender.Proofs.Keccak.SplitThetaXorValues

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def outputBlocks : List Block :=
  (((SourceCaptureTheta.columns[2]?).getD ({ blocks := #[] } : Column)).blocks.toList).take 898

private def xorExpected (index : Nat) : Nat := (index / 256 % 256) ^^^ (index % 256)

private theorem output_length : (outputBlocks.map Block.length).sum = 65536 := by
  setup_source_rfl

private noncomputable def sourceBinding : SourceBank.ColumnBinding :=
  (SourceCaptureTheta.columnBindings[2]'(by change 2 < 9; decide +kernel)).1

private noncomputable def group0 : List Block := [2, 3, 4, 5, 6, 7, 8, 9].map sourceBinding.blocks

private theorem group0_length : (group0.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group0_checked : checkBlockRows xorExpected 0 group0 = true := by decide +kernel

private noncomputable def group1 : List Block := [10, 11, 12, 13, 14, 15, 16, 17].map sourceBinding.blocks

private theorem group1_length : (group1.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group1_checked : checkBlockRows xorExpected 2048 group1 = true := by decide +kernel

private noncomputable def group2 : List Block := [18, 19, 20, 21, 22, 23, 24, 25].map sourceBinding.blocks

private theorem group2_length : (group2.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group2_checked : checkBlockRows xorExpected 4096 group2 = true := by decide +kernel

private noncomputable def group3 : List Block := [26, 27, 28, 29, 30, 31, 32, 33].map sourceBinding.blocks

private theorem group3_length : (group3.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group3_checked : checkBlockRows xorExpected 6144 group3 = true := by decide +kernel

private noncomputable def group4 : List Block := [34, 35, 36, 37, 38, 39, 40, 41].map sourceBinding.blocks

private theorem group4_length : (group4.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group4_checked : checkBlockRows xorExpected 8192 group4 = true := by decide +kernel

private noncomputable def group5 : List Block := [42, 43, 44, 45, 46, 47, 48, 49].map sourceBinding.blocks

private theorem group5_length : (group5.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group5_checked : checkBlockRows xorExpected 10240 group5 = true := by decide +kernel

private noncomputable def group6 : List Block := [50, 51, 52, 53, 54, 55, 56, 57].map sourceBinding.blocks

private theorem group6_length : (group6.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group6_checked : checkBlockRows xorExpected 12288 group6 = true := by decide +kernel

private noncomputable def group7 : List Block := [58, 59, 60, 61, 62, 63, 64, 65].map sourceBinding.blocks

private theorem group7_length : (group7.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group7_checked : checkBlockRows xorExpected 14336 group7 = true := by decide +kernel

private noncomputable def group8 : List Block := [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97].map sourceBinding.blocks

private theorem group8_length : (group8.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group8_checked : checkBlockRows xorExpected 16384 group8 = true := by decide +kernel

private noncomputable def group9 : List Block := [98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129].map sourceBinding.blocks

private theorem group9_length : (group9.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group9_checked : checkBlockRows xorExpected 18432 group9 = true := by decide +kernel

private noncomputable def group10 : List Block := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322].map sourceBinding.blocks

private theorem group10_length : (group10.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group10_checked : checkBlockRows xorExpected 20480 group10 = true := by decide +kernel

private noncomputable def group11 : List Block := [323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386].map sourceBinding.blocks

private theorem group11_length : (group11.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group11_checked : checkBlockRows xorExpected 22528 group11 = true := by decide +kernel

private noncomputable def group12 : List Block := [387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402].map sourceBinding.blocks

private theorem group12_length : (group12.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group12_checked : checkBlockRows xorExpected 24576 group12 = true := by decide +kernel

private noncomputable def group13 : List Block := [403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418].map sourceBinding.blocks

private theorem group13_length : (group13.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group13_checked : checkBlockRows xorExpected 26624 group13 = true := by decide +kernel

private noncomputable def group14 : List Block := [419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434].map sourceBinding.blocks

private theorem group14_length : (group14.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group14_checked : checkBlockRows xorExpected 28672 group14 = true := by decide +kernel

private noncomputable def group15 : List Block := [435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450].map sourceBinding.blocks

private theorem group15_length : (group15.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group15_checked : checkBlockRows xorExpected 30720 group15 = true := by decide +kernel

private noncomputable def group16 : List Block := [451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466].map sourceBinding.blocks

private theorem group16_length : (group16.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group16_checked : checkBlockRows xorExpected 32768 group16 = true := by decide +kernel

private noncomputable def group17 : List Block := [467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482].map sourceBinding.blocks

private theorem group17_length : (group17.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group17_checked : checkBlockRows xorExpected 34816 group17 = true := by decide +kernel

private noncomputable def group18 : List Block := [483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498].map sourceBinding.blocks

private theorem group18_length : (group18.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group18_checked : checkBlockRows xorExpected 36864 group18 = true := by decide +kernel

private noncomputable def group19 : List Block := [499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514].map sourceBinding.blocks

private theorem group19_length : (group19.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group19_checked : checkBlockRows xorExpected 38912 group19 = true := by decide +kernel

private noncomputable def group20 : List Block := [515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578].map sourceBinding.blocks

private theorem group20_length : (group20.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group20_checked : checkBlockRows xorExpected 40960 group20 = true := by decide +kernel

private noncomputable def group21 : List Block := [579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771].map sourceBinding.blocks

private theorem group21_length : (group21.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group21_checked : checkBlockRows xorExpected 43008 group21 = true := by decide +kernel

private noncomputable def group22 : List Block := [772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803].map sourceBinding.blocks

private theorem group22_length : (group22.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group22_checked : checkBlockRows xorExpected 45056 group22 = true := by decide +kernel

private noncomputable def group23 : List Block := [804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835].map sourceBinding.blocks

private theorem group23_length : (group23.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group23_checked : checkBlockRows xorExpected 47104 group23 = true := by decide +kernel

private noncomputable def group24 : List Block := [836, 837, 838, 839, 840, 841, 842, 843].map sourceBinding.blocks

private theorem group24_length : (group24.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group24_checked : checkBlockRows xorExpected 49152 group24 = true := by decide +kernel

private noncomputable def group25 : List Block := [844, 845, 846, 847, 848, 849, 850, 851].map sourceBinding.blocks

private theorem group25_length : (group25.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group25_checked : checkBlockRows xorExpected 51200 group25 = true := by decide +kernel

private noncomputable def group26 : List Block := [852, 853, 854, 855, 856, 857, 858, 859].map sourceBinding.blocks

private theorem group26_length : (group26.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group26_checked : checkBlockRows xorExpected 53248 group26 = true := by decide +kernel

private noncomputable def group27 : List Block := [860, 861, 862, 863, 864, 865, 866, 867].map sourceBinding.blocks

private theorem group27_length : (group27.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group27_checked : checkBlockRows xorExpected 55296 group27 = true := by decide +kernel

private noncomputable def group28 : List Block := [868, 869, 870, 871, 872, 873, 874, 875].map sourceBinding.blocks

private theorem group28_length : (group28.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group28_checked : checkBlockRows xorExpected 57344 group28 = true := by decide +kernel

private noncomputable def group29 : List Block := [876, 877, 878, 879, 880, 881, 882, 883].map sourceBinding.blocks

private theorem group29_length : (group29.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group29_checked : checkBlockRows xorExpected 59392 group29 = true := by decide +kernel

private noncomputable def group30 : List Block := [884, 885, 886, 887, 888, 889, 890, 891].map sourceBinding.blocks

private theorem group30_length : (group30.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group30_checked : checkBlockRows xorExpected 61440 group30 = true := by decide +kernel

private noncomputable def group31 : List Block := [892, 893, 894, 895, 896, 897, 898, 899].map sourceBinding.blocks

private theorem group31_length : (group31.map Block.length).sum = 2048 := by setup_source_rfl

private theorem group31_checked : checkBlockRows xorExpected 63488 group31 = true := by decide +kernel

private theorem output_partition : outputBlocks = group0 ++ group1 ++ group2 ++ group3 ++ group4 ++ group5 ++ group6 ++ group7 ++ group8 ++ group9 ++ group10 ++ group11 ++ group12 ++ group13 ++ group14 ++ group15 ++ group16 ++ group17 ++ group18 ++ group19 ++ group20 ++ group21 ++ group22 ++ group23 ++ group24 ++ group25 ++ group26 ++ group27 ++ group28 ++ group29 ++ group30 ++ group31 := by setup_source_rfl

private theorem output_checked : checkBlockRows xorExpected 0 outputBlocks = true := by
  rw [output_partition]
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

/-- The physical source output is the exact XOR of its byte keys. -/
theorem source_xor_output_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[2]?).getD ({ blocks := #[] } : Column)).get? index.val =
      some ((index.val / 256 % 256) ^^^ (index.val % 256)) := by
  change getFromBlocks _ index.val = _
  rw [getFromBlocks_take _ 898 index.val (by
    change index.val < (outputBlocks.map Block.length).sum
    rw [output_length]
    exact index.isLt)]
  change getFromBlocks outputBlocks index.val = _
  simpa only [Nat.zero_add, xorExpected] using checkBlockRows_sound xorExpected outputBlocks 0 index.val
    output_checked (by rw [output_length]; exact index.isLt)

/-- The source output equals its original native literal-tree output. -/
theorem source_xor_output_match (index : Fin 65536) :
    (((SourceCaptureTheta.columns[2]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[2]).value index.val := by
  rw [source_xor_output_get, Option.getD_some,
    Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_output_value]

end Airbender.Setup.SourceCaptureThetaProofs
