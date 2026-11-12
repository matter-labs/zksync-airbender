module
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedNumericData.Part002
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedNumericData.Part004
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedNumericData.Part006
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedNumericData.Part007
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedNumericData.Part012
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

open NumericPolynomialChecks

def numericForward.leaf18 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 198)], [([((1 : Nat), [])], 199)], [([((1 : Nat), [])], 200)], [([((1 : Nat), [])], 201)],
    [([((1 : Nat), [])], 202)], [([((1 : Nat), [])], 203)], [([((1 : Nat), [])], 204)], [([((1 : Nat), [])], 205)],
    [([((1 : Nat), [])], 206)], [([((1 : Nat), [])], 207)], [([((1 : Nat), [])], 208)], [([((1 : Nat), [])], 209)],
    [([((1 : Nat), [])], 210)], [([((1 : Nat), [])], 211)], [([((1 : Nat), [])], 212)], [([((1 : Nat), [])], 213)]]

def numericForward.leaf19 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 214)], [([((1 : Nat), [])], 215)], [([((1 : Nat), [])], 216)], [([((1 : Nat), [])], 217)],
    [([((1 : Nat), [])], 218)], [([((1 : Nat), [])], 219)], [], [], [], [], []]

def numericForward : List (List (NumericPolynomialChecks.Data × Nat)) :=
  List.append
    (List.append
      (List.append (List.append numericForward.leaf0 numericForward.leaf1)
        (List.append numericForward.leaf2 (List.append numericForward.leaf3 numericForward.leaf4)))
      (List.append (List.append numericForward.leaf5 numericForward.leaf6)
        (List.append numericForward.leaf7 (List.append numericForward.leaf8 numericForward.leaf9))))
    (List.append
      (List.append (List.append numericForward.leaf10 numericForward.leaf11)
        (List.append numericForward.leaf12 (List.append numericForward.leaf13 numericForward.leaf14)))
      (List.append (List.append numericForward.leaf15 numericForward.leaf16)
        (List.append numericForward.leaf17 (List.append numericForward.leaf18 numericForward.leaf19))))

def numericForward.tree : NumericPolynomialChecks.LookupTable (List (NumericPolynomialChecks.Data × Nat)) :=
  NumericPolynomialChecks.LookupTable.branch 160
    (NumericPolynomialChecks.LookupTable.branch 80
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf0)
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf1))
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf2)
          (NumericPolynomialChecks.LookupTable.branch 16
            (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf3)
            (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf4))))
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf5)
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf6))
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf7)
          (NumericPolynomialChecks.LookupTable.branch 16
            (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf8)
            (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf9)))))
    (NumericPolynomialChecks.LookupTable.branch 80
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf10)
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf11))
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf12)
          (NumericPolynomialChecks.LookupTable.branch 16
            (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf13)
            (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf14))))
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf15)
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf16))
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf17)
          (NumericPolynomialChecks.LookupTable.branch 16
            (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf18)
            (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf19)))))

theorem numericForward.tree_binding : (numericForward.tree).toList = numericForward := by kernel_rfl

theorem numericForward.tree_valid : (numericForward.tree).valid = true := by kernel_rfl

def numericKeys : List Nat :=
  [0, 1, 2, 3, 4, 5, 8, 9, 10, 16, 17, 25, 26, 36, 37, 38, 49, 50, 64, 65, 81, 82, 100, 101, 121, 122, 144, 145, 146,
    169, 170, 196, 197, 225, 226, 256, 257, 289, 290, 324, 325, 361, 362, 400, 401, 402, 441, 442, 484, 485, 529, 530,
    576, 577, 625, 626, 676, 677, 729, 730, 784, 785, 841, 842, 900, 901, 902, 961, 962, 1024, 1025, 1089, 1090, 1156,
    1157, 1225, 1226, 1296, 1297, 1369, 1370, 1444, 1445, 1521, 1522, 1600, 1601, 1681, 1682, 1764, 1765, 1766, 1849,
    1850, 1936, 1937, 2025, 2026, 2116, 2117, 2209, 2210, 2304, 2305, 2401, 2402, 2500, 2501, 2601, 2602, 2704, 2705,
    2809, 2810, 2916, 2917, 3025, 3026, 3136, 3137, 3249, 3250, 3364, 3365, 3481, 3482, 3600, 3601, 3721, 3722, 3844,
    3845, 3969, 3970, 4096, 4097, 4225, 4226, 4356, 4357, 4489, 4490, 4624, 4625, 4761, 4762, 4900, 4901, 5041, 5042,
    5184, 5185, 5329, 5330, 5476, 5477, 5625, 5626, 5776, 5777, 5929, 5930, 6084, 6085, 6241, 6242, 6400, 6401, 6561,
    6562, 6724, 6725, 6889, 6890, 7056, 7057, 7225, 7226, 7396, 7397, 7569, 7570, 7744, 7745, 7921, 7922, 8100, 8101,
    8281, 8282, 8464, 8465, 8649, 8650, 8836, 8837, 9025, 9026, 9216, 9217, 9409, 9410, 9604, 9605, 9801, 9802, 10000,
    10001, 10201, 10202, 10404, 10405, 10609, 10610, 10816, 10817, 11025, 11026, 11236, 11237, 11449, 11450, 11664,
    11665, 11881, 11882, 12100, 12101, 12321, 12322, 12544, 12545, 12769, 12770, 12996, 12997, 13225, 13226, 13456,
    13457, 13689, 13690, 13924, 13925, 14161, 14162, 14400, 14401, 14641, 14642, 14884, 14885, 15129, 15130, 15376,
    15377, 15625, 15626, 15876, 15877, 16129, 16130, 16384, 16385, 16641, 16642, 16900, 16901, 17161, 17162, 17424,
    17425, 17689, 17690, 17956, 17957, 18225, 18226, 18496, 18497, 18769, 18770, 19044, 19045, 19321, 19322, 19600,
    19601, 19881, 19882, 20164, 20165, 20449, 20450, 20736, 20737, 21025, 21026, 21316, 21317, 21609, 21610, 21904,
    21905, 22201, 22202, 22500, 22501, 22801, 22802, 23104, 23105, 23409, 23410, 23716, 23717, 24025, 24026, 24336,
    24337, 24649, 24650, 24964, 24965, 25281, 25282, 25600, 25601, 25921, 25922, 26244, 26245, 26569, 26570, 26896,
    26897, 27225, 27226, 27556, 27557, 27889, 27890, 28224, 28225, 28561, 28562, 28900, 28901, 29241, 29242, 29584,
    29585, 29929, 29930, 30276, 30277, 30625, 30626, 30976, 30977, 31329, 31330, 31684, 31685, 32041, 32042, 32400,
    32401, 32761, 32762, 33124, 33125, 33489, 33490, 33856, 33857, 34225, 34226, 34596, 34597, 34969, 34970, 35344,
    35345, 35721, 35722, 36100, 36101, 36481, 36482, 36864, 36865, 37249, 37250, 37636, 37637, 38025, 38026, 38416,
    38417, 38809, 38810, 39204, 39205, 39601, 39602, 40000, 40001, 40401, 40402, 40804, 40805, 41209, 41210, 41616,
    41617, 42025, 42026, 42436, 42437, 42849, 42850, 43264, 43265, 43681, 43682, 44100, 44101, 44521, 44522, 44944,
    44945, 45369, 45370, 45796, 45797, 46225, 46226, 46656, 46657, 47089, 47090, 47524, 47525, 47961, 47962, 48400,
    48401, 48841, 48842, 49284, 49285, 49729, 49730, 50176, 50177, 50625, 51076, 51529, 51984, 52441, 52900, 53361,
    53824, 54289, 54756, 55225, 55696, 56169, 56644, 57121, 57600, 58081, 58564, 59049, 59536, 60025, 60516, 61009,
    61504, 62001, 62500, 63001, 63504, 64009, 64516, 65025, 65536, 66049, 66564, 67081, 67600, 68121, 68644, 69169,
    69696, 70225, 70756, 71289, 71824, 72361, 72900, 73441, 73984, 74529, 75076, 75625, 76176, 76729, 77284, 77841,
    78400, 78961, 79524, 80089, 80656, 81225, 81796, 82369, 82944, 83521, 84100, 84681, 85264, 85849, 86436, 87025,
    87616, 88209, 88804, 89401, 90000, 90601, 91204, 91809, 92416, 93025, 93636, 94249, 94864, 95481, 96100, 96721,
    97344, 97969, 98596, 99225, 99856, 100489, 101124, 101761, 102400, 103041, 103684, 104329, 104976, 105625, 106276,
    106929, 107584, 108241, 108900, 109561, 110224, 110889, 111556, 112225, 112896, 113569, 114244, 114921, 115600,
    116281, 116964, 117649, 118336, 119025, 119716, 120409, 121104, 121801, 122500, 123201, 123904, 124609, 125316,
    126025, 126736, 127449, 128164, 128881, 129600, 130321, 131044, 131769, 132496, 133225, 133956, 134689, 135424,
    136161, 136900, 137641, 138384, 139129, 139876, 140625, 141376, 142129, 142884, 143641, 144400, 145161, 145924,
    146689, 147456, 148225, 148996, 149769, 150544, 151321, 152100, 152881, 153664, 154449, 155236, 156025, 156816,
    157609, 158404, 159201, 160000, 160801, 161604, 162409, 163216, 164025, 164836, 165649, 166464, 167281, 168100,
    168921, 169744, 170569, 171396, 172225, 173056, 173889, 174724, 175561, 176400, 177241, 178084, 178929, 179776,
    180625, 181476, 182329, 183184, 184041, 184900, 185761, 186624, 187489, 188356, 189225, 190096, 190969, 191844,
    192721, 193600, 194481, 195364, 196249, 197136, 198025, 198916, 199809, 200704, 201601, 202500, 203401, 204304,
    205209, 206116, 207025, 207936, 208849, 209764, 210681, 211600, 212521, 213444, 214369, 215296, 216225, 217156,
    218089, 219024, 219961, 220900, 221841, 222784, 223729, 224676, 225625, 226576, 227529, 228484, 229441, 230400,
    231361, 232324, 233289, 234256, 235225, 236196, 237169, 238144, 239121, 240100, 241081, 242064, 243049, 244036,
    245025, 246016, 247009, 248004, 249001, 250000, 251001, 252004, 253009, 254016, 255025, 256036, 257049, 258064,
    259081, 260100, 261121, 262144, 263169, 264196, 265225, 266256, 267289, 268324, 269361, 270400, 271441, 272484,
    273529, 274576, 275625, 276676, 277729, 278784, 279841, 280900, 281961, 283024, 284089, 285156, 286225, 287296,
    288369, 59969542, 62742247, 65610006, 68574967, 71639302, 74805207, 78074902, 81450631, 84934662, 88529287,
    92236822, 96059607, 100000006, 104060407, 108243222, 112550887, 116985862, 121550631, 126247702, 131079607,
    136048902, 141158167, 146410006, 151807047, 157351942, 163047367, 168896022, 174900631, 181063942, 187388727,
    193877782, 200533927, 207360006, 214358887, 221533462, 228886647, 236421382, 244140631, 252047382, 260144647,
    268435462, 276922887, 285610006, 294499927, 303595782, 312900727, 322417942, 332150631, 342102022, 352275367,
    362673942, 373301047, 384160006, 395254167, 406586902, 418161607, 429981702, 442050631, 454371862, 466948887,
    479785222, 492884407, 506250006, 519885607, 533794822, 547981287, 562448662, 577200631, 592240902, 607573207,
    623201302, 639128967, 655360006, 671898247, 688747542, 705911767, 723394822, 741200631, 759333142, 777796327,
    796594182, 815730727, 835210006, 855036087, 875213062, 895745047, 916636182, 937890631, 959512582]

theorem numericSource_binding : native.artifact.source.map encode = numericSource := by kernel_rfl

theorem numericNormalizedSource_binding :
    numericSource.map (NumericPolynomialChecks.normalize babyBearModulus) = numericNormalizedSource := by kernel_rfl

theorem numericLowered_binding : native.artifact.translation.lowered.map encode = numericLowered := by kernel_rfl

theorem numericExtensionData_binding : native.extensionData.toList.map encode = numericExtensionData := by kernel_rfl

theorem numericBackward_binding : native.backwardData.toList.map encodeCombination = numericBackward := by kernel_rfl

theorem numericForward_binding : native.forwardData.toList.map encodeCombination = numericForward := by kernel_rfl
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
