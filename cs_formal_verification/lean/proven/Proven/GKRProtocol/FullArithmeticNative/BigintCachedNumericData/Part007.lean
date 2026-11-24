module
public import Proven.KernelRfl
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part006
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation
public import Proven.Import.GKRProtocol.NumericExpressionDataImport
public import Proven.GKRProtocol.FastNumericNormalization

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

open NumericPolynomialChecks

def numericBackward.leaf6 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 137)], [([((1 : Nat), [])], 138)], [([((1 : Nat), [])], 139)], [([((1 : Nat), [])], 140)],
    [([((1 : Nat), [])], 141)], [([((1 : Nat), [])], 142)], [([((1 : Nat), [])], 143)], [([((1 : Nat), [])], 144)],
    [([((1 : Nat), [])], 145)], [([((1 : Nat), [])], 146)], [([((1 : Nat), [])], 147)], [([((1 : Nat), [])], 148)],
    [([((1 : Nat), [])], 149)], [([((1 : Nat), [])], 150)], [([((1 : Nat), [])], 151)], [([((1 : Nat), [])], 152)]]

def numericBackward.leaf7 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 153)], [([((1 : Nat), [])], 154)], [([((1 : Nat), [])], 155)], [([((1 : Nat), [])], 156)],
    [([((1 : Nat), [])], 157)], [([((1 : Nat), [])], 158)], [([((1 : Nat), [])], 159)], [([((1 : Nat), [])], 160)],
    [([((1 : Nat), [])], 161)], [([((1 : Nat), [])], 162)], [([((1 : Nat), [])], 163)], [([((1 : Nat), [])], 164)],
    [([((1 : Nat), [])], 165)], [([((1 : Nat), [])], 166)], [([((1 : Nat), [])], 167)], [([((1 : Nat), [])], 168)]]

def numericBackward.leaf8 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 169)], [([((1 : Nat), [])], 170)], [([((1 : Nat), [])], 171)], [([((1 : Nat), [])], 172)],
    [([((1 : Nat), [])], 173)], [([((1 : Nat), [])], 174)], [([((1 : Nat), [])], 175)]]

def numericBackward : List (List (NumericPolynomialChecks.Data × Nat)) :=
  List.append
    (List.append (List.append numericBackward.leaf0 numericBackward.leaf1)
      (List.append numericBackward.leaf2 numericBackward.leaf3))
    (List.append (List.append numericBackward.leaf4 numericBackward.leaf5)
      (List.append numericBackward.leaf6 (List.append numericBackward.leaf7 numericBackward.leaf8)))

def numericBackward.tree : NumericPolynomialChecks.LookupTable (List (NumericPolynomialChecks.Data × Nat)) :=
  NumericPolynomialChecks.LookupTable.branch 64
    (NumericPolynomialChecks.LookupTable.branch 32
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf0)
        (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf1))
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf2)
        (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf3)))
    (NumericPolynomialChecks.LookupTable.branch 32
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf4)
        (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf5))
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf6)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf7)
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf8))))

theorem numericBackward.tree_binding : (numericBackward.tree).toList = numericBackward := by kernel_rfl

theorem numericBackward.tree_valid : (numericBackward.tree).valid = true := by kernel_rfl

def numericForward.leaf0 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def numericForward.leaf1 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def numericForward.leaf2 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [([((1 : Nat), [])], 51)], [([((1 : Nat), [])], 52)],
    [([((1 : Nat), [])], 53)], [([((1 : Nat), [])], 54)], [([((1 : Nat), [])], 55)], [([((1 : Nat), [])], 56)]]

def numericForward.leaf3 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 57)], [([((1 : Nat), [])], 58)], [([((1 : Nat), [])], 59)], [([((1 : Nat), [])], 60)],
    [([((1 : Nat), [])], 61)], [([((1 : Nat), [])], 62)], [([((1 : Nat), [])], 63)], [([((1 : Nat), [])], 64)],
    [([((1 : Nat), [])], 65)], [([((1 : Nat), [])], 66)], [([((1 : Nat), [])], 83)], [([((1 : Nat), [])], 84)],
    [([((1 : Nat), [])], 85)], [], [([((1 : Nat), [])], 0)], [([((1 : Nat), [])], 1)]]

def numericForward.leaf4 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 2)], [([((1 : Nat), [])], 3)], [([((1 : Nat), [])], 4)], [([((1 : Nat), [])], 5)],
    [([((1 : Nat), [])], 6)], [([((1 : Nat), [])], 7)], [([((1 : Nat), [])], 8)], [([((1 : Nat), [])], 9)],
    [([((1 : Nat), [])], 10)], [([((1 : Nat), [])], 11)], [([((1 : Nat), [])], 12)], [([((1 : Nat), [])], 13)],
    [([((1 : Nat), [])], 14)], [([((1 : Nat), [])], 15)], [([((1 : Nat), [])], 16)], [([((1 : Nat), [])], 17)]]

def numericForward.leaf5 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 18)], [([((1 : Nat), [])], 19)], [([((1 : Nat), [])], 20)], [([((1 : Nat), [])], 21)],
    [([((1 : Nat), [])], 22)], [([((1 : Nat), [])], 23)], [([((1 : Nat), [])], 24)], [([((1 : Nat), [])], 25)],
    [([((1 : Nat), [])], 26)], [([((1 : Nat), [])], 27)], [([((1 : Nat), [])], 28)], [([((1 : Nat), [])], 29)],
    [([((1 : Nat), [])], 30)], [([((1 : Nat), [])], 31)], [([((1 : Nat), [])], 32)], [([((1 : Nat), [])], 33)]]

def numericForward.leaf6 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 34)], [([((1 : Nat), [])], 35)], [([((1 : Nat), [])], 36)], [([((1 : Nat), [])], 37)],
    [([((1 : Nat), [])], 38)], [([((1 : Nat), [])], 39)], [([((1 : Nat), [])], 40)], [([((1 : Nat), [])], 41)],
    [([((1 : Nat), [])], 42)], [([((1 : Nat), [])], 43)], [([((1 : Nat), [])], 44)], [([((1 : Nat), [])], 45)],
    [([((1 : Nat), [])], 46)], [([((1 : Nat), [])], 47)], [([((1 : Nat), [])], 48)], [([((1 : Nat), [])], 49)]]

def numericForward.leaf7 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 50)], [([((1 : Nat), [])], 67)], [([((1 : Nat), [])], 68)], [([((1 : Nat), [])], 69)],
    [([((1 : Nat), [])], 70)], [([((1 : Nat), [])], 71)], [([((1 : Nat), [])], 72)], [([((1 : Nat), [])], 73)],
    [([((1 : Nat), [])], 74)], [([((1 : Nat), [])], 75)], [([((1 : Nat), [])], 76)], [([((1 : Nat), [])], 77)],
    [([((1 : Nat), [])], 78)], [([((1 : Nat), [])], 79)], [([((1 : Nat), [])], 80)], [([((1 : Nat), [])], 81)]]

def numericForward.leaf8 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 82)], [([((1 : Nat), [])], 88)], [([((1 : Nat), [])], 89)], [([((1 : Nat), [])], 90)],
    [([((1 : Nat), [])], 91)], [([((1 : Nat), [])], 92)], [([((1 : Nat), [])], 93)], [([((1 : Nat), [])], 94)],
    [([((1 : Nat), [])], 95)], [([((1 : Nat), [])], 96)], [([((1 : Nat), [])], 97)], [([((1 : Nat), [])], 98)],
    [([((1 : Nat), [])], 99)], [([((1 : Nat), [])], 100)], [([((1 : Nat), [])], 101)], [([((1 : Nat), [])], 102)]]

def numericForward.leaf9 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 103)], [([((1 : Nat), [])], 104)], [([((1 : Nat), [])], 105)], [([((1 : Nat), [])], 106)],
    [([((1 : Nat), [])], 107)], [([((1 : Nat), [])], 108)], [([((1 : Nat), [])], 109)], [([((1 : Nat), [])], 110)],
    [([((1 : Nat), [])], 111)], [([((1 : Nat), [])], 112)], [([((1 : Nat), [])], 113)], [([((1 : Nat), [])], 114)],
    [([((1 : Nat), [])], 115)], [([((1 : Nat), [])], 116)], [([((1 : Nat), [])], 117)], [([((1 : Nat), [])], 118)]]

def numericForward.leaf10 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 119)], [([((1 : Nat), [])], 120)], [([((1 : Nat), [])], 121)], [([((1 : Nat), [])], 122)],
    [([((1 : Nat), [])], 123)], [([((1 : Nat), [])], 124)], [([((1 : Nat), [])], 125)], [([((1 : Nat), [])], 126)],
    [([((1 : Nat), [])], 127)], [([((1 : Nat), [])], 128)], [([((1 : Nat), [])], 129)], [([((1 : Nat), [])], 130)],
    [([((1 : Nat), [])], 131)], [([((1 : Nat), [])], 132)], [([((1 : Nat), [])], 133)], [([((1 : Nat), [])], 134)]]

def numericForward.leaf11 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [([((1 : Nat), [])], 86)], [([((1 : Nat), [])], 87)], [], [], []]

def numericForward : List (List (NumericPolynomialChecks.Data × Nat)) :=
  List.append
    (List.append (List.append numericForward.leaf0 (List.append numericForward.leaf1 numericForward.leaf2))
      (List.append numericForward.leaf3 (List.append numericForward.leaf4 numericForward.leaf5)))
    (List.append (List.append numericForward.leaf6 (List.append numericForward.leaf7 numericForward.leaf8))
      (List.append numericForward.leaf9 (List.append numericForward.leaf10 numericForward.leaf11)))

def numericForward.tree : NumericPolynomialChecks.LookupTable (List (NumericPolynomialChecks.Data × Nat)) :=
  NumericPolynomialChecks.LookupTable.branch 96
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf0)
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf1)
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf2)))
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf3)
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf4)
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf5))))
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf6)
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf7)
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf8)))
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf9)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf10)
          (NumericPolynomialChecks.LookupTable.leaf numericForward.leaf11))))

theorem numericForward.tree_binding : (numericForward.tree).toList = numericForward := by kernel_rfl

theorem numericForward.tree_valid : (numericForward.tree).valid = true := by kernel_rfl

def numericKeys : List Nat :=
  [0, 1, 2, 3, 4, 5, 8, 9, 10, 16, 17, 25, 26, 36, 37, 38, 49, 50, 64, 65, 81, 82, 100, 101, 121, 122, 144, 145, 146,
    169, 170, 196, 197, 225, 226, 256, 257, 289, 290, 324, 325, 361, 362, 400, 401, 402, 441, 442, 484, 485, 529, 530,
    576, 577, 625, 626, 676, 677, 729, 730, 784, 785, 841, 842, 900, 901, 902, 961, 962, 1024, 1025, 1089, 1090, 1156,
    1157, 1225, 1226, 1296, 1297, 1369, 1370, 1444, 1445, 1521, 1522, 1600, 1601, 1681, 1682, 1764, 1765, 1849, 1850,
    1936, 1937, 2025, 2026, 2116, 2117, 2209, 2210, 2304, 2305, 2401, 2402, 2500, 2501, 2601, 2602, 2704, 2705, 2809,
    2810, 2916, 2917, 3025, 3026, 3136, 3137, 3249, 3250, 3364, 3365, 3481, 3482, 3600, 3601, 3721, 3722, 3844, 3845,
    3969, 3970, 4096, 4097, 4225, 4226, 4356, 4357, 4489, 4490, 4624, 4625, 4761, 4762, 4900, 4901, 5041, 5042, 5184,
    5185, 5329, 5330, 5476, 5477, 5625, 5626, 5776, 5777, 5929, 5930, 6084, 6085, 6241, 6242, 6400, 6401, 6561, 6562,
    6724, 6725, 6889, 6890, 7056, 7057, 7225, 7226, 7396, 7397, 7569, 7570, 7744, 7745, 7921, 7922, 8100, 8101, 8281,
    8282, 8464, 8465, 8649, 8650, 8836, 8837, 9025, 9026, 9216, 9217, 9409, 9604, 9801, 10000, 10201, 10404, 10609,
    10816, 11025, 11236, 11449, 11664, 11881, 12100, 12321, 12544, 12769, 12996, 13225, 13456, 13689, 13924, 14161,
    14400, 14641, 14884, 15129, 15376, 15625, 15876, 16129, 16384, 16641, 16900, 17161, 17424, 17689, 17956, 18225,
    18496, 18769, 19044, 19321, 19600, 19881, 20164, 20449, 20736, 21025, 21316, 21609, 21904, 22201, 22500, 22801,
    23104, 23409, 23716, 24025, 24336, 24649, 24964, 25281, 195366, 235227, 280902, 332931, 391878, 458331, 532902,
    616227, 708966, 811803, 925446, 1050627, 1188102, 1338651, 1503078, 1682211, 1876902, 2088027, 2316486, 2560006,
    2825767, 3111702, 3418807, 3748102, 4100631, 4477462, 4879687, 5308422, 5764807, 6250006, 6765207, 7311622, 7890487,
    8503062, 9150631, 9834502, 9840771, 10556007, 11316502, 12117367, 12960006, 13845847, 14776342, 15752967, 16777222,
    17850631, 18974742, 20151127, 21381382, 22667127, 24010006, 25411687, 26873862, 28398247, 29986582, 31640631,
    33362182, 35153047, 37015062, 38950087, 40960006]
end Airbender.Compiler.FullArithmeticNative.BigintCached
