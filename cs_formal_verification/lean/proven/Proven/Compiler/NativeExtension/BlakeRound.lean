module
public import Proven.Compiler.NativeInputPlacement
public import Proven.Compiler.NativeExtension.BlakeRound.Batch000
public import Proven.Compiler.NativeExtension.BlakeRound.Batch001
public import Proven.Compiler.NativeExtension.BlakeRound.Batch002
public import Proven.Compiler.NativeExtension.BlakeRound.Batch003
public import Proven.Compiler.NativeExtension.BlakeRound.Batch004
public import Proven.Compiler.NativeExtension.BlakeRound.Batch005
public import Proven.Compiler.NativeExtension.BlakeRound.Batch006
public import Proven.Compiler.NativeExtension.BlakeRound.Batch007
public import Proven.Compiler.NativeExtension.BlakeRound.Batch008
public import Proven.Compiler.NativeExtension.BlakeRound.Batch009
public import Proven.Compiler.NativeExtension.BlakeRound.Batch010
public import Proven.Compiler.NativeExtension.BlakeRound.Batch011
public import Proven.Compiler.NativeExtension.BlakeRound.Batch012
public import Proven.Compiler.NativeExtension.BlakeRound.Batch013
public import Proven.Compiler.NativeExtension.BlakeRound.Batch014
public import Proven.Compiler.NativeExtension.BlakeRound.Batch015
public import Proven.Compiler.NativeExtension.BlakeRound.Batch016
public import Proven.Compiler.NativeExtension.BlakeRound.Batch017
public import Proven.Compiler.NativeExtension.BlakeRound.Batch018
public import Proven.Compiler.NativeExtension.BlakeRound.Batch019

@[expose] public section
namespace Airbender.Compiler.NativeExtension.BlakeRound
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The source extension satisfies every actual cached scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (batch000 physical holds) (append_zero (batch001 physical holds) (append_zero (batch002 physical holds) (append_zero (batch003 physical holds) (append_zero (batch004 physical holds) (append_zero (batch005 physical holds) (append_zero (batch006 physical holds) (append_zero (batch007 physical holds) (append_zero (batch008 physical holds) (append_zero (batch009 physical holds) (append_zero (batch010 physical holds) (append_zero (batch011 physical holds) (append_zero (batch012 physical holds) (append_zero (batch013 physical holds) (append_zero (batch014 physical holds) (append_zero (batch015 physical holds) (append_zero (batch016 physical holds) (append_zero (batch017 physical holds) (append_zero (batch018 physical holds) (append_zero (batch019 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))))))

end Airbender.Compiler.NativeExtension.BlakeRound

namespace Airbender.Compiler.NativeExtension.BlakeRound
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 65536

/-- Each native input names its captured logical column. -/
def inputLogicalIndices : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 634, 637, 640, 643, 646, 649, 652, 655, 658, 661, 664, 667, 670, 673, 676, 679, 682, 685, 688, 691, 694, 697, 700, 703, 706, 709, 712, 715, 718, 721, 724, 727, 730, 733, 736, 739, 742, 745, 748, 751, 754, 757, 760, 761, 762, 632, 633, 635, 636, 638, 639, 641, 642, 644, 645, 647, 648, 650, 651, 653, 654, 656, 657, 659, 660, 662, 663, 665, 666, 668, 669, 671, 672, 674, 675, 677, 678, 680, 681, 683, 684, 686, 687, 689, 690, 692, 693, 695, 696, 698, 699, 701, 702, 704, 705, 707, 708, 710, 711, 713, 714, 716, 717, 719, 720, 722, 723, 725, 726, 728, 729, 731, 732, 734, 735, 737, 738, 740, 741, 743, 744, 746, 747, 749, 750, 752, 753, 755, 756, 758, 759]

/-- Read the source inputs in their actual native bank order. -/
noncomputable def inputValues (logical : Nat → F) (index : Fin 763) : F :=
  logical ((inputLogicalIndices[index.val]?).getD 0)

/-- The native extension retains the supplied values at every source placement. -/
theorem extension_preserves (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.BlakeRoundCached.native.artifact.source (inputValues logical)) :
    ∃ physical : GKRAddress → F, Holds Captures.BlakeRound.imported.circuit physical ∧
      PlacementAgreement Captures.BlakeRound.imported.circuit physical logical := by
  let values : Fin 763 → F := inputValues logical
  let extended := FullArithmeticNative.BlakeRoundCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.BlakeRoundCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.BlakeRoundCached.native.full_arithmetic_extends values holds
  refine ⟨physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.BlakeRoundCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · apply NativePlacementWitness.agrees_with_reindexed_inputs
      FullArithmeticNative.BlakeRoundCached.native.inputs (by decide) inputLogicalIndices _ (by decide +kernel)
    intro index
    exact WireBank.materialize_source_input _ FullArithmeticNative.BlakeRoundCached.native.inputBank
      _ FullArithmeticNative.BlakeRoundCached.native.inputCoordinates FullArithmeticNative.BlakeRoundCached.native.bankRoundTrip
      values extended facts.1 (fun _ => 0) index

theorem extension (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.BlakeRoundCached.native.artifact.source
      (fun index => logical index.val)) :
    ∃ (physical : GKRAddress → F) (realized : Nat → F), Holds Captures.BlakeRound.imported.circuit physical ∧
      PlacementAgreement Captures.BlakeRound.imported.circuit physical realized := by
  let values : Fin 763 → F := fun index => logical index.val
  let extended := FullArithmeticNative.BlakeRoundCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.BlakeRoundCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.BlakeRoundCached.native.full_arithmetic_extends values holds
  refine ⟨physical, NativePlacementWitness.assignment Captures.BlakeRound.imported.circuit.placement_data.entries.toList physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.BlakeRoundCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · have keys : Captures.BlakeRound.imported.circuit.placement_data.entries.toList.map Prod.fst =
        List.range 763 := by kernel_rfl
    have unique : (Captures.BlakeRound.imported.circuit.placement_data.entries.toList.map Prod.fst).Nodup := by
      rw [keys]
      exact List.nodup_range
    intro entry member
    exact NativePlacementWitness.agrees _ unique physical entry (by simpa using member)


end Airbender.Compiler.NativeExtension.BlakeRound
