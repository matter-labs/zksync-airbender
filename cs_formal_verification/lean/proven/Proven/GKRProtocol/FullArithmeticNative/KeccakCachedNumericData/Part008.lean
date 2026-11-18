module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part006
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part007
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation
public import Proven.Import.GKRProtocol.NumericExpressionDataImport
public import Proven.GKRProtocol.FastNumericNormalization

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

open NumericPolynomialChecks

theorem numericForward.tree_valid : (numericForward.tree).valid = true := by kernel_rfl

def numericKeys : List Nat :=
  [0, 1, 2, 3, 4, 5, 8, 9, 10, 16, 17, 25, 26, 36, 37, 38, 49, 50, 64, 65, 81, 82, 100, 101, 121, 122, 144, 145, 146,
    169, 170, 196, 197, 225, 226, 256, 257, 289, 290, 324, 325, 361, 362, 400, 401, 402, 441, 442, 484, 485, 529, 530,
    576, 577, 625, 626, 676, 677, 729, 730, 784, 785, 841, 842, 900, 901, 961, 962, 1024, 1025, 1089, 1090, 1156, 1157,
    1225, 1226, 1296, 1297, 1369, 1370, 1444, 1445, 1521, 1522, 1600, 1601, 1681, 1682, 1764, 1765, 1849, 1850, 1936,
    1937, 2025, 2026, 2116, 2117, 2209, 2210, 2304, 2305, 2401, 2402, 2500, 2501, 2601, 2602, 2704, 2705, 2809, 2810,
    2916, 2917, 3025, 3026, 3136, 3137, 3249, 3250, 3364, 3365, 3481, 3482, 3600, 3601, 3721, 3722, 3844, 3845, 3969,
    3970, 4096, 4097, 4225, 4226, 4356, 4357, 4489, 4490, 4624, 4625, 4761, 4762, 4900, 4901, 5041, 5042, 5184, 5185,
    5329, 5330, 5476, 5477, 5625, 5626, 5776, 5777, 5929, 5930, 6084, 6085, 6241, 6242, 6400, 6401, 6561, 6562, 6724,
    6725, 6889, 6890, 7056, 7057, 7225, 7226, 7396, 7397, 7569, 7570, 7744, 7745, 7921, 7922, 8100, 8101, 8281, 8464,
    8649, 8836, 9025, 9216, 9409, 9604, 9801, 10000, 10201, 10404, 10609, 10816, 11025, 11236, 11449, 11664, 11881,
    12100, 12321, 12544, 12769, 12996, 13225, 13456, 13689, 13924, 14161, 14400, 14641, 14884, 15129, 15376, 15625,
    15876, 16129, 16384, 16641, 16900, 17161, 17424, 17689, 17956, 18225, 18496, 18769, 19044, 19321, 19600, 19881,
    20164, 20449, 20736, 21025, 21316, 21609, 21904, 22201, 22500, 22801, 23104, 23409, 23716, 24025, 24336, 24649,
    24964, 25281, 25600, 25921, 26244, 26569, 26896, 27225, 27556, 27889, 28224, 28561, 28900, 29241, 29584, 29929,
    30276, 810006, 923527, 1048582, 1185927, 1336342, 1500631, 1679622, 1874167, 2085142, 2313447, 2560006, 2825767,
    3111702, 3418807, 3748102, 4100631, 4477462, 4879687, 5308422, 5764807, 5769606, 6250006, 6765207, 7311622, 7890487,
    8503062, 9150631, 9834502, 10556007, 11316502, 12117367]

theorem numericLowered_binding : native.artifact.translation.lowered.map encode = numericLowered := by kernel_rfl

theorem numericExtensionData_binding : native.extensionData.toList.map encode = numericExtensionData := by kernel_rfl

theorem numericBackward_binding : native.backwardData.toList.map encodeCombination = numericBackward := by kernel_rfl

theorem numericForward_binding : native.forwardData.toList.map encodeCombination = numericForward := by kernel_rfl

def numericSourceHelpers.leaf0 : List NumericPolynomialChecks.Data :=
  [[((1 : Nat), [222, 222]), ((2013265920 : Nat), [222])], [((1 : Nat), [223, 223]), ((2013265920 : Nat), [223])],
    [((1 : Nat), [224, 224]), ((2013265920 : Nat), [224])], [((1 : Nat), [225, 225]), ((2013265920 : Nat), [225])],
    [((1 : Nat), [226, 226]), ((2013265920 : Nat), [226])], [((1 : Nat), [227, 227]), ((2013265920 : Nat), [227])],
    [((1 : Nat), [228, 228]), ((2013265920 : Nat), [228])], [((1 : Nat), [229, 229]), ((2013265920 : Nat), [229])],
    [((1 : Nat), [230, 230]), ((2013265920 : Nat), [230])], [((1 : Nat), [231, 231]), ((2013265920 : Nat), [231])],
    [((1 : Nat), [232, 232]), ((2013265920 : Nat), [232])], [((1 : Nat), [233, 233]), ((2013265920 : Nat), [233])],
    [((1 : Nat), [234, 234]), ((2013265920 : Nat), [234])], [((1 : Nat), [235, 235]), ((2013265920 : Nat), [235])]]

def numericSourceHelpers : List NumericPolynomialChecks.Data :=
  numericSourceHelpers.leaf0

def numericSourceHelpers.tree : NumericPolynomialChecks.LookupTable NumericPolynomialChecks.Data :=
  NumericPolynomialChecks.LookupTable.leaf numericSourceHelpers.leaf0

theorem numericSourceHelpers.tree_binding : (numericSourceHelpers.tree).toList = numericSourceHelpers := by kernel_rfl

theorem numericSourceHelpers.tree_valid : (numericSourceHelpers.tree).valid = true := by kernel_rfl

def numericSourceExpressions.node0 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.add
    (NumericExpressionChecks.Code.add
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                (NumericExpressionChecks.Code.atom 64))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.constant 2))
                (NumericExpressionChecks.Code.atom 65)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 3))
              (NumericExpressionChecks.Code.atom 66)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 4))
            (NumericExpressionChecks.Code.atom 67)))
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.constant 5))
          (NumericExpressionChecks.Code.atom 68)))
      (NumericExpressionChecks.Code.mul
        (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
          (NumericExpressionChecks.Code.constant 6))
        (NumericExpressionChecks.Code.atom 69)))
    (NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.constant 8))
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.atom 71))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 2))
              (NumericExpressionChecks.Code.atom 72)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 3))
            (NumericExpressionChecks.Code.atom 73)))
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.constant 4))
          (NumericExpressionChecks.Code.atom 74))))

def numericSourceExpressions.node1 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.add
    (NumericExpressionChecks.Code.add
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add
                    (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                      (NumericExpressionChecks.Code.atom 64))
                    (NumericExpressionChecks.Code.mul
                      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                        (NumericExpressionChecks.Code.constant 2))
                      (NumericExpressionChecks.Code.atom 65)))
                  (NumericExpressionChecks.Code.mul
                    (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                      (NumericExpressionChecks.Code.constant 3))
                    (NumericExpressionChecks.Code.atom 66)))
                (NumericExpressionChecks.Code.mul
                  (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                    (NumericExpressionChecks.Code.constant 4))
                  (NumericExpressionChecks.Code.atom 67)))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.constant 5))
                (NumericExpressionChecks.Code.atom 68)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 6))
              (NumericExpressionChecks.Code.atom 69)))
          (NumericExpressionChecks.Code.atom 64))
        (NumericExpressionChecks.Code.atom 65))
      (NumericExpressionChecks.Code.atom 68))
    (NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.atom 63))
            (NumericExpressionChecks.Code.atom 66))
          (NumericExpressionChecks.Code.atom 67)))
      (NumericExpressionChecks.Code.atom 74))

def numericSourceExpressions.node2 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.add
    (NumericExpressionChecks.Code.add numericSourceExpressions.node1
      (NumericExpressionChecks.Code.mul
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.constant 2013265920))
          (NumericExpressionChecks.Code.atom 69))
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.constant 1))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 5))
            (NumericExpressionChecks.Code.atom 74)))))
    (NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.constant 8))
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                (NumericExpressionChecks.Code.atom 71))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.constant 2))
                (NumericExpressionChecks.Code.atom 72)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 3))
              (NumericExpressionChecks.Code.atom 73)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 4))
            (NumericExpressionChecks.Code.atom 74)))
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                    (NumericExpressionChecks.Code.atom 63))
                  (NumericExpressionChecks.Code.atom 66))
                (NumericExpressionChecks.Code.atom 67))
              (NumericExpressionChecks.Code.atom 69)))
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.constant 1))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 2013265916))
              (NumericExpressionChecks.Code.atom 74))))))

def numericSourceExpressions.node3 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.mul
    (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                    (NumericExpressionChecks.Code.atom 64))
                  (NumericExpressionChecks.Code.atom 65))
                (NumericExpressionChecks.Code.atom 80))
              (NumericExpressionChecks.Code.atom 81))
            (NumericExpressionChecks.Code.atom 83))
          (NumericExpressionChecks.Code.atom 84))
        (NumericExpressionChecks.Code.atom 82)))
    (NumericExpressionChecks.Code.add
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
        (NumericExpressionChecks.Code.atom 102))
      (NumericExpressionChecks.Code.mul
        (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
          (NumericExpressionChecks.Code.constant 2013200385))
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                    (NumericExpressionChecks.Code.atom 64))
                  (NumericExpressionChecks.Code.atom 65))
                (NumericExpressionChecks.Code.atom 81))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.atom 82))
                (NumericExpressionChecks.Code.constant 14)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.atom 83))
              (NumericExpressionChecks.Code.constant 12)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.atom 84))
            (NumericExpressionChecks.Code.constant 11)))))

def numericSourceExpressions.node4 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.add
    (NumericExpressionChecks.Code.add
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                (NumericExpressionChecks.Code.constant 1))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.constant 2013265920))
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add
                    (NumericExpressionChecks.Code.add
                      (NumericExpressionChecks.Code.add
                        (NumericExpressionChecks.Code.add
                          (NumericExpressionChecks.Code.add
                            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                              (NumericExpressionChecks.Code.atom 64))
                            (NumericExpressionChecks.Code.atom 65))
                          (NumericExpressionChecks.Code.atom 80))
                        (NumericExpressionChecks.Code.atom 81))
                      (NumericExpressionChecks.Code.atom 83))
                    (NumericExpressionChecks.Code.atom 84))
                  (NumericExpressionChecks.Code.atom 82)))))
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.atom 102))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 256))
              (NumericExpressionChecks.Code.atom 103)))))
      numericSourceExpressions.node3)
    (NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.constant 2013265920))
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                    (NumericExpressionChecks.Code.mul
                      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                        (NumericExpressionChecks.Code.atom 15))
                      (NumericExpressionChecks.Code.atom 63)))
                  (NumericExpressionChecks.Code.mul
                    (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                      (NumericExpressionChecks.Code.atom 15))
                    (NumericExpressionChecks.Code.atom 64)))
                (NumericExpressionChecks.Code.mul
                  (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                    (NumericExpressionChecks.Code.atom 23))
                  (NumericExpressionChecks.Code.atom 65)))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.atom 15))
                (NumericExpressionChecks.Code.atom 66)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.atom 15))
              (NumericExpressionChecks.Code.atom 67)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.atom 15))
            (NumericExpressionChecks.Code.atom 68)))
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.atom 31))
          (NumericExpressionChecks.Code.atom 69))))

def numericSourceExpressions.node5 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.add
    (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
      (NumericExpressionChecks.Code.mul
        (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.constant 1))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 2013265920))
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add
                    (NumericExpressionChecks.Code.add
                      (NumericExpressionChecks.Code.add
                        (NumericExpressionChecks.Code.add
                          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                            (NumericExpressionChecks.Code.atom 64))
                          (NumericExpressionChecks.Code.atom 65))
                        (NumericExpressionChecks.Code.atom 80))
                      (NumericExpressionChecks.Code.atom 81))
                    (NumericExpressionChecks.Code.atom 83))
                  (NumericExpressionChecks.Code.atom 84))
                (NumericExpressionChecks.Code.atom 82)))))
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 110))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 256))
            (NumericExpressionChecks.Code.atom 111)))))
    (NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.constant 2013265920))
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.atom 86))
                (NumericExpressionChecks.Code.atom 63)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.atom 55))
              (NumericExpressionChecks.Code.atom 66)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.atom 23))
            (NumericExpressionChecks.Code.atom 68)))
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.atom 15))
          (NumericExpressionChecks.Code.atom 69))))

def numericSourceExpressions.node6 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.add
    (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
      (NumericExpressionChecks.Code.mul
        (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.constant 1))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 2013265920))
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add
                    (NumericExpressionChecks.Code.add
                      (NumericExpressionChecks.Code.add
                        (NumericExpressionChecks.Code.add
                          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                            (NumericExpressionChecks.Code.atom 64))
                          (NumericExpressionChecks.Code.atom 65))
                        (NumericExpressionChecks.Code.atom 80))
                      (NumericExpressionChecks.Code.atom 81))
                    (NumericExpressionChecks.Code.atom 83))
                  (NumericExpressionChecks.Code.atom 84))
                (NumericExpressionChecks.Code.atom 82)))))
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 118))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 256))
            (NumericExpressionChecks.Code.atom 119)))))
    (NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                (NumericExpressionChecks.Code.atom 64))
              (NumericExpressionChecks.Code.atom 65))
            (NumericExpressionChecks.Code.atom 80))
          (NumericExpressionChecks.Code.atom 81)))
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
          (NumericExpressionChecks.Code.atom 118))
        (NumericExpressionChecks.Code.atom 113)))

def numericSourceExpressions.node7 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.add
    (NumericExpressionChecks.Code.add
      (NumericExpressionChecks.Code.add numericSourceExpressions.node6
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                (NumericExpressionChecks.Code.atom 83))
              (NumericExpressionChecks.Code.atom 84)))
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.atom 121))
            (NumericExpressionChecks.Code.atom 112))))
      (NumericExpressionChecks.Code.mul
        (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
          (NumericExpressionChecks.Code.atom 82))
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 119))
          (NumericExpressionChecks.Code.atom 110))))
    (NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.constant 2013265920))
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                    (NumericExpressionChecks.Code.mul
                      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                        (NumericExpressionChecks.Code.atom 17))
                      (NumericExpressionChecks.Code.atom 63)))
                  (NumericExpressionChecks.Code.mul
                    (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                      (NumericExpressionChecks.Code.atom 57))
                    (NumericExpressionChecks.Code.atom 64)))
                (NumericExpressionChecks.Code.mul
                  (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                    (NumericExpressionChecks.Code.atom 90))
                  (NumericExpressionChecks.Code.atom 65)))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.atom 17))
                (NumericExpressionChecks.Code.atom 66)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.atom 17))
              (NumericExpressionChecks.Code.atom 67)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.atom 49))
            (NumericExpressionChecks.Code.atom 68)))
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.atom 90))
          (NumericExpressionChecks.Code.atom 69))))

def numericSourceExpressions.node8 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.mul
    (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                    (NumericExpressionChecks.Code.atom 64))
                  (NumericExpressionChecks.Code.atom 65))
                (NumericExpressionChecks.Code.atom 80))
              (NumericExpressionChecks.Code.atom 81))
            (NumericExpressionChecks.Code.atom 83))
          (NumericExpressionChecks.Code.atom 84))
        (NumericExpressionChecks.Code.atom 82)))
    (NumericExpressionChecks.Code.add
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
        (NumericExpressionChecks.Code.atom 103))
      (NumericExpressionChecks.Code.mul
        (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
          (NumericExpressionChecks.Code.constant 2013200385))
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                    (NumericExpressionChecks.Code.atom 64))
                  (NumericExpressionChecks.Code.atom 65))
                (NumericExpressionChecks.Code.atom 81))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.atom 82))
                (NumericExpressionChecks.Code.constant 14)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.atom 83))
              (NumericExpressionChecks.Code.constant 12)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.atom 84))
            (NumericExpressionChecks.Code.constant 11)))))

def numericSourceExpressions.node9 : NumericExpressionChecks.Code :=
  NumericExpressionChecks.Code.add
    (NumericExpressionChecks.Code.add
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                (NumericExpressionChecks.Code.constant 1))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.constant 2013265920))
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add
                    (NumericExpressionChecks.Code.add
                      (NumericExpressionChecks.Code.add
                        (NumericExpressionChecks.Code.add
                          (NumericExpressionChecks.Code.add
                            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                              (NumericExpressionChecks.Code.atom 64))
                            (NumericExpressionChecks.Code.atom 65))
                          (NumericExpressionChecks.Code.atom 80))
                        (NumericExpressionChecks.Code.atom 81))
                      (NumericExpressionChecks.Code.atom 83))
                    (NumericExpressionChecks.Code.atom 84))
                  (NumericExpressionChecks.Code.atom 82)))))
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
              (NumericExpressionChecks.Code.atom 104))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.constant 256))
              (NumericExpressionChecks.Code.atom 105)))))
      numericSourceExpressions.node8)
    (NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.constant 2013265920))
      (NumericExpressionChecks.Code.add
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add
            (NumericExpressionChecks.Code.add
              (NumericExpressionChecks.Code.add
                (NumericExpressionChecks.Code.add
                  (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
                    (NumericExpressionChecks.Code.mul
                      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                        (NumericExpressionChecks.Code.atom 16))
                      (NumericExpressionChecks.Code.atom 63)))
                  (NumericExpressionChecks.Code.mul
                    (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                      (NumericExpressionChecks.Code.atom 16))
                    (NumericExpressionChecks.Code.atom 64)))
                (NumericExpressionChecks.Code.mul
                  (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                    (NumericExpressionChecks.Code.atom 24))
                  (NumericExpressionChecks.Code.atom 65)))
              (NumericExpressionChecks.Code.mul
                (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                  (NumericExpressionChecks.Code.atom 16))
                (NumericExpressionChecks.Code.atom 66)))
            (NumericExpressionChecks.Code.mul
              (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
                (NumericExpressionChecks.Code.atom 16))
              (NumericExpressionChecks.Code.atom 67)))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.atom 16))
            (NumericExpressionChecks.Code.atom 68)))
        (NumericExpressionChecks.Code.mul
          (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
            (NumericExpressionChecks.Code.atom 32))
          (NumericExpressionChecks.Code.atom 69))))
end Airbender.Compiler.FullArithmeticNative.KeccakCached
