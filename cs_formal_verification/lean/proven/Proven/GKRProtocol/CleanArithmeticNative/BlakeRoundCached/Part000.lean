module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BlakeRoundCached
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCached
public import Proven.GKRProtocol.CleanPlacementNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch0Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch0Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.relations : List (Polynomial 858 Source.BaseField) :=
  (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact).gates.map ArithmeticGate.inputResidual

def native.placementKeys : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
    61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
    90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114,
    115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137,
    138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
    161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183,
    184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206,
    207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
    230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252,
    253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275,
    276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298,
    299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321,
    322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344,
    345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367,
    368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390,
    391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413,
    414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436,
    437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459,
    460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482,
    483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505,
    506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528,
    529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551,
    552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574,
    575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597,
    598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620,
    621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643,
    644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666,
    667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689,
    690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712,
    713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735,
    736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758,
    759, 760, 761, 762]

def native.placementAddresses.part000 : List GKRAddress := [GKRAddress.BaseLayerMemory 222,
GKRAddress.BaseLayerMemory 223,
GKRAddress.BaseLayerMemory 224,
GKRAddress.BaseLayerMemory 2,
GKRAddress.BaseLayerMemory 3,
GKRAddress.BaseLayerMemory 6,
GKRAddress.BaseLayerMemory 7,
GKRAddress.BaseLayerMemory 8,
GKRAddress.BaseLayerMemory 9,
GKRAddress.BaseLayerMemory 12,
GKRAddress.BaseLayerMemory 13,
GKRAddress.BaseLayerMemory 14,
GKRAddress.BaseLayerMemory 15,
GKRAddress.BaseLayerMemory 18,
GKRAddress.BaseLayerMemory 19,
GKRAddress.BaseLayerMemory 20,
GKRAddress.BaseLayerMemory 21,
GKRAddress.BaseLayerMemory 24,
GKRAddress.BaseLayerMemory 25,
GKRAddress.BaseLayerMemory 26,
GKRAddress.BaseLayerMemory 27,
GKRAddress.BaseLayerMemory 30,
GKRAddress.BaseLayerMemory 31,
GKRAddress.BaseLayerMemory 32,
GKRAddress.BaseLayerMemory 33,
GKRAddress.BaseLayerMemory 36,
GKRAddress.BaseLayerMemory 37,
GKRAddress.BaseLayerMemory 38,
GKRAddress.BaseLayerMemory 39,
GKRAddress.BaseLayerMemory 42,
GKRAddress.BaseLayerMemory 43,
GKRAddress.BaseLayerMemory 44,
GKRAddress.BaseLayerMemory 45,
GKRAddress.BaseLayerMemory 48,
GKRAddress.BaseLayerMemory 49,
GKRAddress.BaseLayerMemory 50,
GKRAddress.BaseLayerMemory 51,
GKRAddress.BaseLayerMemory 54,
GKRAddress.BaseLayerMemory 55,
GKRAddress.BaseLayerMemory 56,
GKRAddress.BaseLayerMemory 57,
GKRAddress.BaseLayerMemory 60,
GKRAddress.BaseLayerMemory 61,
GKRAddress.BaseLayerMemory 62,
GKRAddress.BaseLayerMemory 63,
GKRAddress.BaseLayerMemory 66,
GKRAddress.BaseLayerMemory 67,
GKRAddress.BaseLayerMemory 68,
GKRAddress.BaseLayerMemory 69,
GKRAddress.BaseLayerMemory 72,
GKRAddress.BaseLayerMemory 73,
GKRAddress.BaseLayerMemory 74,
GKRAddress.BaseLayerMemory 75,
GKRAddress.BaseLayerMemory 78,
GKRAddress.BaseLayerMemory 79,
GKRAddress.BaseLayerMemory 80,
GKRAddress.BaseLayerMemory 81,
GKRAddress.BaseLayerMemory 84,
GKRAddress.BaseLayerMemory 85,
GKRAddress.BaseLayerMemory 86,
GKRAddress.BaseLayerMemory 87,
GKRAddress.BaseLayerMemory 90,
GKRAddress.BaseLayerMemory 91,
GKRAddress.BaseLayerMemory 92,
GKRAddress.BaseLayerMemory 93,
GKRAddress.BaseLayerMemory 96,
GKRAddress.BaseLayerMemory 97,
GKRAddress.BaseLayerMemory 98,
GKRAddress.BaseLayerMemory 99,
GKRAddress.BaseLayerMemory 102,
GKRAddress.BaseLayerMemory 103,
GKRAddress.BaseLayerMemory 104,
GKRAddress.BaseLayerMemory 105,
GKRAddress.BaseLayerMemory 108,
GKRAddress.BaseLayerMemory 109,
GKRAddress.BaseLayerMemory 110,
GKRAddress.BaseLayerMemory 111,
GKRAddress.BaseLayerMemory 114,
GKRAddress.BaseLayerMemory 115,
GKRAddress.BaseLayerMemory 116,
GKRAddress.BaseLayerMemory 117,
GKRAddress.BaseLayerMemory 120,
GKRAddress.BaseLayerMemory 121,
GKRAddress.BaseLayerMemory 122,
GKRAddress.BaseLayerMemory 123,
GKRAddress.BaseLayerMemory 126,
GKRAddress.BaseLayerMemory 127,
GKRAddress.BaseLayerMemory 128,
GKRAddress.BaseLayerMemory 129,
GKRAddress.BaseLayerMemory 132,
GKRAddress.BaseLayerMemory 133,
GKRAddress.BaseLayerMemory 134,
GKRAddress.BaseLayerMemory 135,
GKRAddress.BaseLayerMemory 138,
GKRAddress.BaseLayerMemory 139,
GKRAddress.BaseLayerMemory 140,
GKRAddress.BaseLayerMemory 141,
GKRAddress.BaseLayerMemory 144,
GKRAddress.BaseLayerMemory 145,
GKRAddress.BaseLayerMemory 146,
GKRAddress.BaseLayerMemory 147,
GKRAddress.BaseLayerMemory 150,
GKRAddress.BaseLayerMemory 151,
GKRAddress.BaseLayerMemory 154,
GKRAddress.BaseLayerMemory 155,
GKRAddress.BaseLayerMemory 158,
GKRAddress.BaseLayerMemory 159,
GKRAddress.BaseLayerMemory 162,
GKRAddress.BaseLayerMemory 163,
GKRAddress.BaseLayerMemory 166,
GKRAddress.BaseLayerMemory 167,
GKRAddress.BaseLayerMemory 170,
GKRAddress.BaseLayerMemory 171,
GKRAddress.BaseLayerMemory 174,
GKRAddress.BaseLayerMemory 175,
GKRAddress.BaseLayerMemory 178,
GKRAddress.BaseLayerMemory 179,
GKRAddress.BaseLayerMemory 182,
GKRAddress.BaseLayerMemory 183,
GKRAddress.BaseLayerMemory 186,
GKRAddress.BaseLayerMemory 187,
GKRAddress.BaseLayerMemory 190,
GKRAddress.BaseLayerMemory 191,
GKRAddress.BaseLayerMemory 194,
GKRAddress.BaseLayerMemory 195,
GKRAddress.BaseLayerMemory 198,
GKRAddress.BaseLayerMemory 199,
GKRAddress.BaseLayerMemory 202,
GKRAddress.BaseLayerMemory 203,
GKRAddress.BaseLayerMemory 206,
GKRAddress.BaseLayerMemory 207,
GKRAddress.BaseLayerMemory 210,
GKRAddress.BaseLayerMemory 211,
GKRAddress.BaseLayerMemory 214,
GKRAddress.BaseLayerMemory 215,
GKRAddress.BaseLayerMemory 218,
GKRAddress.BaseLayerMemory 219,
GKRAddress.BaseLayerMemory 220,
GKRAddress.BaseLayerMemory 221,
GKRAddress.BaseLayerWitness 0,
GKRAddress.BaseLayerWitness 1,
GKRAddress.BaseLayerWitness 2,
GKRAddress.BaseLayerWitness 3,
GKRAddress.BaseLayerWitness 4,
GKRAddress.BaseLayerWitness 5,
GKRAddress.BaseLayerWitness 6,
GKRAddress.BaseLayerWitness 7,
GKRAddress.BaseLayerWitness 8,
GKRAddress.BaseLayerWitness 9,
GKRAddress.BaseLayerWitness 10,
GKRAddress.BaseLayerWitness 11,
GKRAddress.BaseLayerWitness 12,
GKRAddress.BaseLayerWitness 13,
GKRAddress.BaseLayerWitness 14,
GKRAddress.BaseLayerWitness 15,
GKRAddress.BaseLayerWitness 16,
GKRAddress.BaseLayerWitness 17,
GKRAddress.BaseLayerWitness 18,
GKRAddress.BaseLayerWitness 19,
GKRAddress.BaseLayerWitness 20,
GKRAddress.BaseLayerWitness 21,
GKRAddress.BaseLayerWitness 22,
GKRAddress.BaseLayerWitness 23,
GKRAddress.BaseLayerWitness 24,
GKRAddress.BaseLayerWitness 25,
GKRAddress.BaseLayerWitness 26,
GKRAddress.BaseLayerWitness 27,
GKRAddress.BaseLayerWitness 28,
GKRAddress.BaseLayerWitness 29,
GKRAddress.BaseLayerWitness 30,
GKRAddress.BaseLayerWitness 31,
GKRAddress.BaseLayerWitness 32,
GKRAddress.BaseLayerWitness 33,
GKRAddress.BaseLayerWitness 34,
GKRAddress.BaseLayerWitness 35,
GKRAddress.BaseLayerWitness 36,
GKRAddress.BaseLayerWitness 37,
GKRAddress.BaseLayerWitness 38,
GKRAddress.BaseLayerWitness 39,
GKRAddress.BaseLayerWitness 40,
GKRAddress.BaseLayerWitness 41,
GKRAddress.BaseLayerWitness 42,
GKRAddress.BaseLayerWitness 43,
GKRAddress.BaseLayerWitness 44,
GKRAddress.BaseLayerWitness 45,
GKRAddress.BaseLayerWitness 46,
GKRAddress.BaseLayerWitness 47,
GKRAddress.BaseLayerWitness 48,
GKRAddress.BaseLayerWitness 49,
GKRAddress.BaseLayerWitness 50,
GKRAddress.BaseLayerWitness 51,
GKRAddress.BaseLayerWitness 52,
GKRAddress.BaseLayerWitness 53,
GKRAddress.BaseLayerWitness 54,
GKRAddress.BaseLayerWitness 55,
GKRAddress.BaseLayerWitness 56,
GKRAddress.BaseLayerWitness 57,
GKRAddress.BaseLayerWitness 58,
GKRAddress.BaseLayerWitness 59,
GKRAddress.BaseLayerWitness 60,
GKRAddress.BaseLayerWitness 61,
GKRAddress.BaseLayerWitness 62,
GKRAddress.BaseLayerWitness 63,
GKRAddress.BaseLayerWitness 64,
GKRAddress.BaseLayerWitness 65,
GKRAddress.BaseLayerWitness 66,
GKRAddress.BaseLayerWitness 67,
GKRAddress.BaseLayerWitness 68,
GKRAddress.BaseLayerWitness 69,
GKRAddress.BaseLayerWitness 70,
GKRAddress.BaseLayerWitness 71,
GKRAddress.BaseLayerWitness 72,
GKRAddress.BaseLayerWitness 73,
GKRAddress.BaseLayerWitness 74,
GKRAddress.BaseLayerWitness 75,
GKRAddress.BaseLayerWitness 76,
GKRAddress.BaseLayerWitness 77,
GKRAddress.BaseLayerWitness 78,
GKRAddress.BaseLayerWitness 79,
GKRAddress.BaseLayerWitness 80,
GKRAddress.BaseLayerWitness 81,
GKRAddress.BaseLayerWitness 82,
GKRAddress.BaseLayerWitness 83,
GKRAddress.BaseLayerWitness 84,
GKRAddress.BaseLayerWitness 85,
GKRAddress.BaseLayerWitness 86,
GKRAddress.BaseLayerWitness 87,
GKRAddress.BaseLayerWitness 88,
GKRAddress.BaseLayerWitness 89,
GKRAddress.BaseLayerWitness 90,
GKRAddress.BaseLayerWitness 91,
GKRAddress.BaseLayerWitness 92,
GKRAddress.BaseLayerWitness 93,
GKRAddress.BaseLayerWitness 94,
GKRAddress.BaseLayerWitness 95,
GKRAddress.BaseLayerWitness 96,
GKRAddress.BaseLayerWitness 97,
GKRAddress.BaseLayerWitness 98,
GKRAddress.BaseLayerWitness 99,
GKRAddress.BaseLayerWitness 100,
GKRAddress.BaseLayerWitness 101,
GKRAddress.BaseLayerWitness 102,
GKRAddress.BaseLayerWitness 103,
GKRAddress.BaseLayerWitness 104,
GKRAddress.BaseLayerWitness 105,
GKRAddress.BaseLayerWitness 106,
GKRAddress.BaseLayerWitness 107,
GKRAddress.BaseLayerWitness 108,
GKRAddress.BaseLayerWitness 109,
GKRAddress.BaseLayerWitness 110,
GKRAddress.BaseLayerWitness 111,
GKRAddress.BaseLayerWitness 112,
GKRAddress.BaseLayerWitness 113,
GKRAddress.BaseLayerWitness 114,
GKRAddress.BaseLayerWitness 115,
GKRAddress.BaseLayerWitness 116,
GKRAddress.BaseLayerWitness 117,
GKRAddress.BaseLayerWitness 118,
GKRAddress.BaseLayerWitness 119,
GKRAddress.BaseLayerWitness 120,
GKRAddress.BaseLayerWitness 121,
GKRAddress.BaseLayerWitness 122,
GKRAddress.BaseLayerWitness 123,
GKRAddress.BaseLayerWitness 124,
GKRAddress.BaseLayerWitness 125,
GKRAddress.BaseLayerWitness 126,
GKRAddress.BaseLayerWitness 127,
GKRAddress.BaseLayerWitness 128,
GKRAddress.BaseLayerWitness 129,
GKRAddress.BaseLayerWitness 130,
GKRAddress.BaseLayerWitness 131,
GKRAddress.BaseLayerWitness 132,
GKRAddress.BaseLayerWitness 133,
GKRAddress.BaseLayerWitness 134,
GKRAddress.BaseLayerWitness 135,
GKRAddress.BaseLayerWitness 136,
GKRAddress.BaseLayerWitness 137,
GKRAddress.BaseLayerWitness 138,
GKRAddress.BaseLayerWitness 139,
GKRAddress.BaseLayerWitness 140,
GKRAddress.BaseLayerWitness 141,
GKRAddress.BaseLayerWitness 142,
GKRAddress.BaseLayerWitness 143,
GKRAddress.BaseLayerWitness 144,
GKRAddress.BaseLayerWitness 145,
GKRAddress.BaseLayerWitness 146,
GKRAddress.BaseLayerWitness 147,
GKRAddress.BaseLayerWitness 148,
GKRAddress.BaseLayerWitness 149,
GKRAddress.BaseLayerWitness 150,
GKRAddress.BaseLayerWitness 151,
GKRAddress.BaseLayerWitness 152,
GKRAddress.BaseLayerWitness 153,
GKRAddress.BaseLayerWitness 154,
GKRAddress.BaseLayerWitness 155,
GKRAddress.BaseLayerWitness 156,
GKRAddress.BaseLayerWitness 157,
GKRAddress.BaseLayerWitness 158,
GKRAddress.BaseLayerWitness 159,
GKRAddress.BaseLayerWitness 160,
GKRAddress.BaseLayerWitness 161,
GKRAddress.BaseLayerWitness 162,
GKRAddress.BaseLayerWitness 163,
GKRAddress.BaseLayerWitness 164,
GKRAddress.BaseLayerWitness 165,
GKRAddress.BaseLayerWitness 166,
GKRAddress.BaseLayerWitness 167,
GKRAddress.BaseLayerWitness 168,
GKRAddress.BaseLayerWitness 169,
GKRAddress.BaseLayerWitness 170,
GKRAddress.BaseLayerWitness 171,
GKRAddress.BaseLayerWitness 172,
GKRAddress.BaseLayerWitness 173,
GKRAddress.BaseLayerWitness 174,
GKRAddress.BaseLayerWitness 175,
GKRAddress.BaseLayerWitness 176,
GKRAddress.BaseLayerWitness 177,
GKRAddress.BaseLayerWitness 178,
GKRAddress.BaseLayerWitness 179,
GKRAddress.BaseLayerWitness 180,
GKRAddress.BaseLayerWitness 181,
GKRAddress.BaseLayerWitness 182,
GKRAddress.BaseLayerWitness 183,
GKRAddress.BaseLayerWitness 184,
GKRAddress.BaseLayerWitness 185,
GKRAddress.BaseLayerWitness 186,
GKRAddress.BaseLayerWitness 187,
GKRAddress.BaseLayerWitness 188,
GKRAddress.BaseLayerWitness 189,
GKRAddress.BaseLayerWitness 190,
GKRAddress.BaseLayerWitness 191,
GKRAddress.BaseLayerWitness 192,
GKRAddress.BaseLayerWitness 193,
GKRAddress.BaseLayerWitness 194,
GKRAddress.BaseLayerWitness 195,
GKRAddress.BaseLayerWitness 196,
GKRAddress.BaseLayerWitness 197,
GKRAddress.BaseLayerWitness 198,
GKRAddress.BaseLayerWitness 199,
GKRAddress.BaseLayerWitness 200,
GKRAddress.BaseLayerWitness 201,
GKRAddress.BaseLayerWitness 202,
GKRAddress.BaseLayerWitness 203,
GKRAddress.BaseLayerWitness 204,
GKRAddress.BaseLayerWitness 205,
GKRAddress.BaseLayerWitness 206,
GKRAddress.BaseLayerWitness 207,
GKRAddress.BaseLayerWitness 208,
GKRAddress.BaseLayerWitness 209,
GKRAddress.BaseLayerWitness 210,
GKRAddress.BaseLayerWitness 211,
GKRAddress.BaseLayerWitness 212,
GKRAddress.BaseLayerWitness 213,
GKRAddress.BaseLayerWitness 214,
GKRAddress.BaseLayerWitness 215,
GKRAddress.BaseLayerWitness 216,
GKRAddress.BaseLayerWitness 217,
GKRAddress.BaseLayerWitness 218,
GKRAddress.BaseLayerWitness 219,
GKRAddress.BaseLayerWitness 220,
GKRAddress.BaseLayerWitness 221,
GKRAddress.BaseLayerWitness 222,
GKRAddress.BaseLayerWitness 223,
GKRAddress.BaseLayerWitness 224,
GKRAddress.BaseLayerWitness 225,
GKRAddress.BaseLayerWitness 226,
GKRAddress.BaseLayerWitness 227,
GKRAddress.BaseLayerWitness 228,
GKRAddress.BaseLayerWitness 229,
GKRAddress.BaseLayerWitness 230,
GKRAddress.BaseLayerWitness 231,
GKRAddress.BaseLayerWitness 232,
GKRAddress.BaseLayerWitness 233,
GKRAddress.BaseLayerWitness 234,
GKRAddress.BaseLayerWitness 235,
GKRAddress.BaseLayerWitness 236,
GKRAddress.BaseLayerWitness 237,
GKRAddress.BaseLayerWitness 238,
GKRAddress.BaseLayerWitness 239,
GKRAddress.BaseLayerWitness 240,
GKRAddress.BaseLayerWitness 241,
GKRAddress.BaseLayerWitness 242,
GKRAddress.BaseLayerWitness 243,
GKRAddress.BaseLayerWitness 244,
GKRAddress.BaseLayerWitness 245,
GKRAddress.BaseLayerWitness 246,
GKRAddress.BaseLayerWitness 247,
GKRAddress.BaseLayerWitness 248,
GKRAddress.BaseLayerWitness 249,
GKRAddress.BaseLayerWitness 250,
GKRAddress.BaseLayerWitness 251,
GKRAddress.BaseLayerWitness 252,
GKRAddress.BaseLayerWitness 253,
GKRAddress.BaseLayerWitness 254,
GKRAddress.BaseLayerWitness 255,
GKRAddress.BaseLayerWitness 256,
GKRAddress.BaseLayerWitness 257]

def native.placementAddresses.part001 : List GKRAddress := [GKRAddress.BaseLayerWitness 258,
GKRAddress.BaseLayerWitness 259,
GKRAddress.BaseLayerWitness 260,
GKRAddress.BaseLayerWitness 261,
GKRAddress.BaseLayerWitness 262,
GKRAddress.BaseLayerWitness 263,
GKRAddress.BaseLayerWitness 264,
GKRAddress.BaseLayerWitness 265,
GKRAddress.BaseLayerWitness 266,
GKRAddress.BaseLayerWitness 267,
GKRAddress.BaseLayerWitness 268,
GKRAddress.BaseLayerWitness 269,
GKRAddress.BaseLayerWitness 270,
GKRAddress.BaseLayerWitness 271,
GKRAddress.BaseLayerWitness 272,
GKRAddress.BaseLayerWitness 273,
GKRAddress.BaseLayerWitness 274,
GKRAddress.BaseLayerWitness 275,
GKRAddress.BaseLayerWitness 276,
GKRAddress.BaseLayerWitness 277,
GKRAddress.BaseLayerWitness 278,
GKRAddress.BaseLayerWitness 279,
GKRAddress.BaseLayerWitness 280,
GKRAddress.BaseLayerWitness 281,
GKRAddress.BaseLayerWitness 282,
GKRAddress.BaseLayerWitness 283,
GKRAddress.BaseLayerWitness 284,
GKRAddress.BaseLayerWitness 285,
GKRAddress.BaseLayerWitness 286,
GKRAddress.BaseLayerWitness 287,
GKRAddress.BaseLayerWitness 288,
GKRAddress.BaseLayerWitness 289,
GKRAddress.BaseLayerWitness 290,
GKRAddress.BaseLayerWitness 291,
GKRAddress.BaseLayerWitness 292,
GKRAddress.BaseLayerWitness 293,
GKRAddress.BaseLayerWitness 294,
GKRAddress.BaseLayerWitness 295,
GKRAddress.BaseLayerWitness 296,
GKRAddress.BaseLayerWitness 297,
GKRAddress.BaseLayerWitness 298,
GKRAddress.BaseLayerWitness 299,
GKRAddress.BaseLayerWitness 300,
GKRAddress.BaseLayerWitness 301,
GKRAddress.BaseLayerWitness 302,
GKRAddress.BaseLayerWitness 303,
GKRAddress.BaseLayerWitness 304,
GKRAddress.BaseLayerWitness 305,
GKRAddress.BaseLayerWitness 306,
GKRAddress.BaseLayerWitness 307,
GKRAddress.BaseLayerWitness 308,
GKRAddress.BaseLayerWitness 309,
GKRAddress.BaseLayerWitness 310,
GKRAddress.BaseLayerWitness 311,
GKRAddress.BaseLayerWitness 312,
GKRAddress.BaseLayerWitness 313,
GKRAddress.BaseLayerWitness 314,
GKRAddress.BaseLayerWitness 315,
GKRAddress.BaseLayerWitness 316,
GKRAddress.BaseLayerWitness 317,
GKRAddress.BaseLayerWitness 318,
GKRAddress.BaseLayerWitness 319,
GKRAddress.BaseLayerWitness 320,
GKRAddress.BaseLayerWitness 321,
GKRAddress.BaseLayerWitness 322,
GKRAddress.BaseLayerWitness 323,
GKRAddress.BaseLayerWitness 324,
GKRAddress.BaseLayerWitness 325,
GKRAddress.BaseLayerWitness 326,
GKRAddress.BaseLayerWitness 327,
GKRAddress.BaseLayerWitness 328,
GKRAddress.BaseLayerWitness 329,
GKRAddress.BaseLayerWitness 330,
GKRAddress.BaseLayerWitness 331,
GKRAddress.BaseLayerWitness 332,
GKRAddress.BaseLayerWitness 333,
GKRAddress.BaseLayerWitness 334,
GKRAddress.BaseLayerWitness 335,
GKRAddress.BaseLayerWitness 336,
GKRAddress.BaseLayerWitness 337,
GKRAddress.BaseLayerWitness 338,
GKRAddress.BaseLayerWitness 339,
GKRAddress.BaseLayerWitness 340,
GKRAddress.BaseLayerWitness 341,
GKRAddress.BaseLayerWitness 342,
GKRAddress.BaseLayerWitness 343,
GKRAddress.BaseLayerWitness 344,
GKRAddress.BaseLayerWitness 345,
GKRAddress.BaseLayerWitness 346,
GKRAddress.BaseLayerWitness 347,
GKRAddress.BaseLayerWitness 348,
GKRAddress.BaseLayerWitness 349,
GKRAddress.BaseLayerWitness 350,
GKRAddress.BaseLayerWitness 351,
GKRAddress.BaseLayerWitness 352,
GKRAddress.BaseLayerWitness 353,
GKRAddress.BaseLayerWitness 354,
GKRAddress.BaseLayerWitness 355,
GKRAddress.BaseLayerWitness 356,
GKRAddress.BaseLayerWitness 357,
GKRAddress.BaseLayerWitness 358,
GKRAddress.BaseLayerWitness 359,
GKRAddress.BaseLayerWitness 360,
GKRAddress.BaseLayerWitness 361,
GKRAddress.BaseLayerWitness 362,
GKRAddress.BaseLayerWitness 363,
GKRAddress.BaseLayerWitness 364,
GKRAddress.BaseLayerWitness 365,
GKRAddress.BaseLayerWitness 366,
GKRAddress.BaseLayerWitness 367,
GKRAddress.BaseLayerWitness 368,
GKRAddress.BaseLayerWitness 369,
GKRAddress.BaseLayerWitness 370,
GKRAddress.BaseLayerWitness 371,
GKRAddress.BaseLayerWitness 372,
GKRAddress.BaseLayerWitness 373,
GKRAddress.BaseLayerWitness 374,
GKRAddress.BaseLayerWitness 375,
GKRAddress.BaseLayerWitness 376,
GKRAddress.BaseLayerWitness 377,
GKRAddress.BaseLayerWitness 378,
GKRAddress.BaseLayerWitness 379,
GKRAddress.BaseLayerWitness 380,
GKRAddress.BaseLayerWitness 381,
GKRAddress.BaseLayerWitness 382,
GKRAddress.BaseLayerWitness 383,
GKRAddress.BaseLayerWitness 384,
GKRAddress.BaseLayerWitness 385,
GKRAddress.BaseLayerWitness 386,
GKRAddress.BaseLayerWitness 387,
GKRAddress.BaseLayerWitness 388,
GKRAddress.BaseLayerWitness 389,
GKRAddress.BaseLayerWitness 390,
GKRAddress.BaseLayerWitness 391,
GKRAddress.BaseLayerWitness 392,
GKRAddress.BaseLayerWitness 393,
GKRAddress.BaseLayerWitness 394,
GKRAddress.BaseLayerWitness 395,
GKRAddress.BaseLayerWitness 396,
GKRAddress.BaseLayerWitness 397,
GKRAddress.BaseLayerWitness 398,
GKRAddress.BaseLayerWitness 399,
GKRAddress.BaseLayerWitness 400,
GKRAddress.BaseLayerWitness 401,
GKRAddress.BaseLayerWitness 402,
GKRAddress.BaseLayerWitness 403,
GKRAddress.BaseLayerWitness 404,
GKRAddress.BaseLayerWitness 405,
GKRAddress.BaseLayerWitness 406,
GKRAddress.BaseLayerWitness 407,
GKRAddress.BaseLayerWitness 408,
GKRAddress.BaseLayerWitness 409,
GKRAddress.BaseLayerWitness 410,
GKRAddress.BaseLayerWitness 411,
GKRAddress.BaseLayerWitness 412,
GKRAddress.BaseLayerWitness 413,
GKRAddress.BaseLayerWitness 414,
GKRAddress.BaseLayerWitness 415,
GKRAddress.BaseLayerWitness 416,
GKRAddress.BaseLayerWitness 417,
GKRAddress.BaseLayerWitness 418,
GKRAddress.BaseLayerWitness 419,
GKRAddress.BaseLayerWitness 420,
GKRAddress.BaseLayerWitness 421,
GKRAddress.BaseLayerWitness 422,
GKRAddress.BaseLayerWitness 423,
GKRAddress.BaseLayerWitness 424,
GKRAddress.BaseLayerWitness 425,
GKRAddress.BaseLayerWitness 426,
GKRAddress.BaseLayerWitness 427,
GKRAddress.BaseLayerWitness 428,
GKRAddress.BaseLayerWitness 429,
GKRAddress.BaseLayerWitness 430,
GKRAddress.BaseLayerWitness 431,
GKRAddress.BaseLayerWitness 432,
GKRAddress.BaseLayerWitness 433,
GKRAddress.BaseLayerWitness 434,
GKRAddress.BaseLayerWitness 435,
GKRAddress.BaseLayerWitness 436,
GKRAddress.BaseLayerWitness 437,
GKRAddress.BaseLayerWitness 438,
GKRAddress.BaseLayerWitness 439,
GKRAddress.BaseLayerWitness 440,
GKRAddress.BaseLayerWitness 441,
GKRAddress.BaseLayerWitness 442,
GKRAddress.BaseLayerWitness 443,
GKRAddress.BaseLayerWitness 444,
GKRAddress.BaseLayerWitness 445,
GKRAddress.BaseLayerWitness 446,
GKRAddress.BaseLayerWitness 447,
GKRAddress.BaseLayerWitness 448,
GKRAddress.BaseLayerWitness 449,
GKRAddress.BaseLayerWitness 450,
GKRAddress.BaseLayerWitness 451,
GKRAddress.BaseLayerWitness 452,
GKRAddress.BaseLayerWitness 453,
GKRAddress.BaseLayerWitness 454,
GKRAddress.BaseLayerWitness 455,
GKRAddress.BaseLayerWitness 456,
GKRAddress.BaseLayerWitness 457,
GKRAddress.BaseLayerWitness 458,
GKRAddress.BaseLayerWitness 459,
GKRAddress.BaseLayerWitness 460,
GKRAddress.BaseLayerWitness 461,
GKRAddress.BaseLayerWitness 462,
GKRAddress.BaseLayerWitness 463,
GKRAddress.BaseLayerWitness 464,
GKRAddress.BaseLayerWitness 465,
GKRAddress.BaseLayerWitness 466,
GKRAddress.BaseLayerWitness 467,
GKRAddress.BaseLayerWitness 468,
GKRAddress.BaseLayerWitness 469,
GKRAddress.BaseLayerWitness 470,
GKRAddress.BaseLayerWitness 471,
GKRAddress.BaseLayerWitness 472,
GKRAddress.BaseLayerWitness 473,
GKRAddress.BaseLayerWitness 474,
GKRAddress.BaseLayerWitness 475,
GKRAddress.BaseLayerWitness 476,
GKRAddress.BaseLayerWitness 477,
GKRAddress.BaseLayerWitness 478,
GKRAddress.BaseLayerWitness 479,
GKRAddress.BaseLayerWitness 480,
GKRAddress.BaseLayerWitness 481,
GKRAddress.BaseLayerWitness 482,
GKRAddress.BaseLayerWitness 483,
GKRAddress.BaseLayerWitness 484,
GKRAddress.BaseLayerWitness 485,
GKRAddress.BaseLayerWitness 486,
GKRAddress.BaseLayerWitness 487,
GKRAddress.BaseLayerWitness 488,
GKRAddress.BaseLayerWitness 489,
GKRAddress.BaseLayerWitness 490,
GKRAddress.BaseLayerWitness 491,
GKRAddress.BaseLayerWitness 492,
GKRAddress.BaseLayerMemory 0,
GKRAddress.BaseLayerMemory 1,
GKRAddress.BaseLayerWitness 493,
GKRAddress.BaseLayerMemory 4,
GKRAddress.BaseLayerMemory 5,
GKRAddress.BaseLayerWitness 494,
GKRAddress.BaseLayerMemory 10,
GKRAddress.BaseLayerMemory 11,
GKRAddress.BaseLayerWitness 495,
GKRAddress.BaseLayerMemory 16,
GKRAddress.BaseLayerMemory 17,
GKRAddress.BaseLayerWitness 496,
GKRAddress.BaseLayerMemory 22,
GKRAddress.BaseLayerMemory 23,
GKRAddress.BaseLayerWitness 497,
GKRAddress.BaseLayerMemory 28,
GKRAddress.BaseLayerMemory 29,
GKRAddress.BaseLayerWitness 498,
GKRAddress.BaseLayerMemory 34,
GKRAddress.BaseLayerMemory 35,
GKRAddress.BaseLayerWitness 499,
GKRAddress.BaseLayerMemory 40,
GKRAddress.BaseLayerMemory 41,
GKRAddress.BaseLayerWitness 500,
GKRAddress.BaseLayerMemory 46,
GKRAddress.BaseLayerMemory 47,
GKRAddress.BaseLayerWitness 501,
GKRAddress.BaseLayerMemory 52,
GKRAddress.BaseLayerMemory 53,
GKRAddress.BaseLayerWitness 502,
GKRAddress.BaseLayerMemory 58,
GKRAddress.BaseLayerMemory 59,
GKRAddress.BaseLayerWitness 503,
GKRAddress.BaseLayerMemory 64,
GKRAddress.BaseLayerMemory 65,
GKRAddress.BaseLayerWitness 504,
GKRAddress.BaseLayerMemory 70,
GKRAddress.BaseLayerMemory 71,
GKRAddress.BaseLayerWitness 505,
GKRAddress.BaseLayerMemory 76,
GKRAddress.BaseLayerMemory 77,
GKRAddress.BaseLayerWitness 506,
GKRAddress.BaseLayerMemory 82,
GKRAddress.BaseLayerMemory 83,
GKRAddress.BaseLayerWitness 507,
GKRAddress.BaseLayerMemory 88,
GKRAddress.BaseLayerMemory 89,
GKRAddress.BaseLayerWitness 508,
GKRAddress.BaseLayerMemory 94,
GKRAddress.BaseLayerMemory 95,
GKRAddress.BaseLayerWitness 509,
GKRAddress.BaseLayerMemory 100,
GKRAddress.BaseLayerMemory 101,
GKRAddress.BaseLayerWitness 510,
GKRAddress.BaseLayerMemory 106,
GKRAddress.BaseLayerMemory 107,
GKRAddress.BaseLayerWitness 511,
GKRAddress.BaseLayerMemory 112,
GKRAddress.BaseLayerMemory 113,
GKRAddress.BaseLayerWitness 512,
GKRAddress.BaseLayerMemory 118,
GKRAddress.BaseLayerMemory 119,
GKRAddress.BaseLayerWitness 513,
GKRAddress.BaseLayerMemory 124,
GKRAddress.BaseLayerMemory 125,
GKRAddress.BaseLayerWitness 514,
GKRAddress.BaseLayerMemory 130,
GKRAddress.BaseLayerMemory 131,
GKRAddress.BaseLayerWitness 515,
GKRAddress.BaseLayerMemory 136,
GKRAddress.BaseLayerMemory 137,
GKRAddress.BaseLayerWitness 516,
GKRAddress.BaseLayerMemory 142,
GKRAddress.BaseLayerMemory 143,
GKRAddress.BaseLayerWitness 517,
GKRAddress.BaseLayerMemory 148,
GKRAddress.BaseLayerMemory 149,
GKRAddress.BaseLayerWitness 518,
GKRAddress.BaseLayerMemory 152,
GKRAddress.BaseLayerMemory 153,
GKRAddress.BaseLayerWitness 519,
GKRAddress.BaseLayerMemory 156,
GKRAddress.BaseLayerMemory 157,
GKRAddress.BaseLayerWitness 520,
GKRAddress.BaseLayerMemory 160,
GKRAddress.BaseLayerMemory 161,
GKRAddress.BaseLayerWitness 521,
GKRAddress.BaseLayerMemory 164,
GKRAddress.BaseLayerMemory 165,
GKRAddress.BaseLayerWitness 522,
GKRAddress.BaseLayerMemory 168,
GKRAddress.BaseLayerMemory 169,
GKRAddress.BaseLayerWitness 523,
GKRAddress.BaseLayerMemory 172,
GKRAddress.BaseLayerMemory 173,
GKRAddress.BaseLayerWitness 524,
GKRAddress.BaseLayerMemory 176,
GKRAddress.BaseLayerMemory 177,
GKRAddress.BaseLayerWitness 525,
GKRAddress.BaseLayerMemory 180,
GKRAddress.BaseLayerMemory 181,
GKRAddress.BaseLayerWitness 526,
GKRAddress.BaseLayerMemory 184,
GKRAddress.BaseLayerMemory 185,
GKRAddress.BaseLayerWitness 527,
GKRAddress.BaseLayerMemory 188,
GKRAddress.BaseLayerMemory 189,
GKRAddress.BaseLayerWitness 528,
GKRAddress.BaseLayerMemory 192,
GKRAddress.BaseLayerMemory 193,
GKRAddress.BaseLayerWitness 529,
GKRAddress.BaseLayerMemory 196,
GKRAddress.BaseLayerMemory 197,
GKRAddress.BaseLayerWitness 530,
GKRAddress.BaseLayerMemory 200,
GKRAddress.BaseLayerMemory 201,
GKRAddress.BaseLayerWitness 531,
GKRAddress.BaseLayerMemory 204,
GKRAddress.BaseLayerMemory 205,
GKRAddress.BaseLayerWitness 532,
GKRAddress.BaseLayerMemory 208,
GKRAddress.BaseLayerMemory 209,
GKRAddress.BaseLayerWitness 533,
GKRAddress.BaseLayerMemory 212,
GKRAddress.BaseLayerMemory 213,
GKRAddress.BaseLayerWitness 534,
GKRAddress.BaseLayerMemory 216,
GKRAddress.BaseLayerMemory 217,
GKRAddress.BaseLayerWitness 535,
GKRAddress.BaseLayerWitness 536,
GKRAddress.BaseLayerWitness 537]

def native.placementAddresses : List GKRAddress := native.placementAddresses.part000 ++ native.placementAddresses.part001

theorem native.placementsRange : native.placementKeys = List.range 763 := by kernel_rfl

theorem native.placementsUnique : (native.placementKeys).Nodup :=
  by
  rw [native.placementsRange]
  exact List.nodup_range

theorem native.placementsSourceBinding :
    native.placementAddresses = Airbender.Compiler.CleanPlacementNative.BlakeRoundCached.placements := by kernel_rfl

theorem native.placementsInBank :
    ((native.placementAddresses).all fun address : GKRAddress =>
        decide
          ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
              ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
            address)) =
      true :=
  (congrArg
        (fun items : List GKRAddress =>
          items.all fun address : GKRAddress =>
            decide
              ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                  ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
                address))
        native.placementsSourceBinding).trans
    Airbender.Compiler.CleanPlacementNative.BlakeRoundCached.placementsInBank

theorem native.placementInBank0 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 222) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 0 (GKRAddress.BaseLayerMemory 222) (by rfl)

theorem native.placementInBank1 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 223) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 1 (GKRAddress.BaseLayerMemory 223) (by rfl)

theorem native.placementInBank2 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 224) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 2 (GKRAddress.BaseLayerMemory 224) (by rfl)

theorem native.placementInBank3 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 2) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 3 (GKRAddress.BaseLayerMemory 2) (by rfl)

theorem native.placementInBank4 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 3) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 4 (GKRAddress.BaseLayerMemory 3) (by rfl)

theorem native.placementInBank5 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 6) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 5 (GKRAddress.BaseLayerMemory 6) (by rfl)

theorem native.placementInBank6 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 7) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 6 (GKRAddress.BaseLayerMemory 7) (by rfl)

theorem native.placementInBank7 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 8) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 7 (GKRAddress.BaseLayerMemory 8) (by rfl)

theorem native.placementInBank8 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 9) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 8 (GKRAddress.BaseLayerMemory 9) (by rfl)

theorem native.placementInBank9 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 12) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 9 (GKRAddress.BaseLayerMemory 12) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
