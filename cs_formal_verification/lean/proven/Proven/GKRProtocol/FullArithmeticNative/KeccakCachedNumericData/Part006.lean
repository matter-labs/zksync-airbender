module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part003
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part004
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part005
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

def numericLowered.leaf10 : List NumericPolynomialChecks.Data :=
  [[((0 : Nat), []), ((1 : Nat), [67, 55]), ((2013265920 : Nat), [67, 57])],
    [((0 : Nat), []), ((1 : Nat), [67, 56]), ((2013265920 : Nat), [67, 58])],
    [((0 : Nat), []), ((1 : Nat), [67, 59]), ((2013265920 : Nat), [67, 61])],
    [((0 : Nat), []), ((1 : Nat), [67, 60]), ((2013265920 : Nat), [67, 62])],
    [((0 : Nat), []), ((1 : Nat), [68, 15]), ((2013265920 : Nat), [68, 57])],
    [((0 : Nat), []), ((1 : Nat), [68, 16]), ((2013265920 : Nat), [68, 58])],
    [((0 : Nat), []), ((1 : Nat), [68, 19]), ((2013265920 : Nat), [68, 61])],
    [((0 : Nat), []), ((1 : Nat), [68, 20]), ((2013265920 : Nat), [68, 62])],
    [((0 : Nat), []), ((1 : Nat), [68, 31]), ((2013265920 : Nat), [68, 33])],
    [((0 : Nat), []), ((1 : Nat), [68, 32]), ((2013265920 : Nat), [68, 34])],
    [((0 : Nat), []), ((1 : Nat), [68, 35]), ((2013265920 : Nat), [68, 37])],
    [((0 : Nat), []), ((1 : Nat), [68, 36]), ((2013265920 : Nat), [68, 38])],
    [((0 : Nat), []), ((1 : Nat), [68, 39]), ((2013265920 : Nat), [68, 41])],
    [((0 : Nat), []), ((1 : Nat), [68, 40]), ((2013265920 : Nat), [68, 42])],
    [((0 : Nat), []), ((1 : Nat), [68, 43]), ((2013265920 : Nat), [68, 45])],
    [((0 : Nat), []), ((1 : Nat), [68, 44]), ((2013265920 : Nat), [68, 46])]]

def numericLowered.leaf11 : List NumericPolynomialChecks.Data :=
  [[((0 : Nat), []), ((1 : Nat), [69, 39]), ((2013265920 : Nat), [69, 41])],
    [((0 : Nat), []), ((1 : Nat), [69, 40]), ((2013265920 : Nat), [69, 42])],
    [((0 : Nat), []), ((1 : Nat), [69, 43]), ((2013265920 : Nat), [69, 45])],
    [((0 : Nat), []), ((1 : Nat), [69, 44]), ((2013265920 : Nat), [69, 46])],
    [((0 : Nat), []), ((1 : Nat), [69, 47]), ((2013265920 : Nat), [69, 49])],
    [((0 : Nat), []), ((1 : Nat), [69, 48]), ((2013265920 : Nat), [69, 50])],
    [((0 : Nat), []), ((1 : Nat), [69, 51]), ((2013265920 : Nat), [69, 53])],
    [((0 : Nat), []), ((1 : Nat), [69, 52]), ((2013265920 : Nat), [69, 54])],
    [((0 : Nat), []), ((1 : Nat), [69, 55]), ((2013265920 : Nat), [69, 57])],
    [((0 : Nat), []), ((1 : Nat), [69, 56]), ((2013265920 : Nat), [69, 58])],
    [((0 : Nat), []), ((1 : Nat), [69, 59]), ((2013265920 : Nat), [69, 61])],
    [((0 : Nat), []), ((1 : Nat), [69, 60]), ((2013265920 : Nat), [69, 62])],
    [((0 : Nat), []), ((2013265920 : Nat), [63]), ((1 : Nat), [63, 63])],
    [((0 : Nat), []), ((2013265920 : Nat), [64]), ((1 : Nat), [64, 64])],
    [((0 : Nat), []), ((2013265920 : Nat), [65]), ((1 : Nat), [65, 65])],
    [((0 : Nat), []), ((2013265920 : Nat), [66]), ((1 : Nat), [66, 66])]]

def numericLowered.leaf12 : List NumericPolynomialChecks.Data :=
  [[((0 : Nat), []), ((2013265920 : Nat), [67]), ((1 : Nat), [67, 67])],
    [((0 : Nat), []), ((2013265920 : Nat), [68]), ((1 : Nat), [68, 68])],
    [((0 : Nat), []), ((2013265920 : Nat), [69]), ((1 : Nat), [69, 69])],
    [((0 : Nat), []), ((2013265920 : Nat), [70]), ((1 : Nat), [70, 70])],
    [((0 : Nat), []), ((2013265920 : Nat), [71]), ((1 : Nat), [71, 71])],
    [((0 : Nat), []), ((2013265920 : Nat), [72]), ((1 : Nat), [72, 72])],
    [((0 : Nat), []), ((2013265920 : Nat), [73]), ((1 : Nat), [73, 73])],
    [((0 : Nat), []), ((2013265920 : Nat), [74]), ((1 : Nat), [74, 74])],
    [((0 : Nat), []), ((2013265920 : Nat), [75]), ((1 : Nat), [75, 75])],
    [((0 : Nat), []), ((2013265920 : Nat), [76]), ((1 : Nat), [76, 76])],
    [((0 : Nat), []), ((2013265920 : Nat), [77]), ((1 : Nat), [77, 77])],
    [((0 : Nat), []), ((2013265920 : Nat), [78]), ((1 : Nat), [78, 78])],
    [((0 : Nat), []), ((2013265920 : Nat), [79]), ((1 : Nat), [79, 79])],
    [((0 : Nat), []), ((2013265920 : Nat), [222]), ((1 : Nat), [222, 222])],
    [((0 : Nat), []), ((2013265920 : Nat), [223]), ((1 : Nat), [223, 223])],
    [((0 : Nat), []), ((2013265920 : Nat), [224]), ((1 : Nat), [224, 224])]]

def numericLowered.leaf13 : List NumericPolynomialChecks.Data :=
  [[((0 : Nat), []), ((2013265920 : Nat), [225]), ((1 : Nat), [225, 225])],
    [((0 : Nat), []), ((2013265920 : Nat), [226]), ((1 : Nat), [226, 226])],
    [((0 : Nat), []), ((2013265920 : Nat), [227]), ((1 : Nat), [227, 227])],
    [((0 : Nat), []), ((2013265920 : Nat), [228]), ((1 : Nat), [228, 228])],
    [((0 : Nat), []), ((2013265920 : Nat), [229]), ((1 : Nat), [229, 229])],
    [((0 : Nat), []), ((2013265920 : Nat), [230]), ((1 : Nat), [230, 230])],
    [((0 : Nat), []), ((2013265920 : Nat), [231]), ((1 : Nat), [231, 231])],
    [((0 : Nat), []), ((2013265920 : Nat), [232]), ((1 : Nat), [232, 232])],
    [((0 : Nat), []), ((2013265920 : Nat), [233]), ((1 : Nat), [233, 233])],
    [((0 : Nat), []), ((2013265920 : Nat), [234]), ((1 : Nat), [234, 234])],
    [((0 : Nat), []), ((2013265920 : Nat), [235]), ((1 : Nat), [235, 235])],
    [((1 : Nat), [269]), ((2013265920 : Nat), [266])], [((1 : Nat), [270]), ((2013265920 : Nat), [269])],
    [((1 : Nat), [271]), ((2013265920 : Nat), [270])]]

def numericLowered : List NumericPolynomialChecks.Data :=
  List.append
    (List.append (List.append numericLowered.leaf0 (List.append numericLowered.leaf1 numericLowered.leaf2))
      (List.append (List.append numericLowered.leaf3 numericLowered.leaf4)
        (List.append numericLowered.leaf5 numericLowered.leaf6)))
    (List.append (List.append numericLowered.leaf7 (List.append numericLowered.leaf8 numericLowered.leaf9))
      (List.append (List.append numericLowered.leaf10 numericLowered.leaf11)
        (List.append numericLowered.leaf12 numericLowered.leaf13)))

def numericLowered.tree : NumericPolynomialChecks.LookupTable NumericPolynomialChecks.Data :=
  NumericPolynomialChecks.LookupTable.branch 112
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf0)
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf1)
          (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf2)))
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf3)
          (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf4))
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf5)
          (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf6))))
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf7)
        (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf8)
          (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf9)))
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf10)
          (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf11))
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf12)
          (NumericPolynomialChecks.LookupTable.leaf numericLowered.leaf13))))

theorem numericLowered.tree_binding : (numericLowered.tree).toList = numericLowered := by kernel_rfl

theorem numericLowered.tree_valid : (numericLowered.tree).valid = true := by kernel_rfl

def numericExtensionData.leaf0 : List NumericPolynomialChecks.Data :=
  [[((1 : Nat), [0])], [((2005401601 : Nat), [13])], [((2005401601 : Nat), [13])], [((1 : Nat), [0])],
    [((1 : Nat), [0])], [((1 : Nat), [0])], [((503316480 : Nat), [0]), ((1509949441 : Nat), [1])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [222]), ((1 : Nat), [238])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [222]), ((1 : Nat), [239])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [223]), ((1 : Nat), [240])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [223]), ((1 : Nat), [241])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [224]), ((1 : Nat), [242])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [224]), ((1 : Nat), [243])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [225]), ((1 : Nat), [244])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [225]), ((1 : Nat), [245])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [226]), ((1 : Nat), [246])]]

def numericExtensionData.leaf1 : List NumericPolynomialChecks.Data :=
  [[((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [226]), ((1 : Nat), [247])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [227]), ((1 : Nat), [248])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [227]), ((1 : Nat), [249])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [228]), ((1 : Nat), [250])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [228]), ((1 : Nat), [251])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [229]), ((1 : Nat), [252])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [229]), ((1 : Nat), [253])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [230]), ((1 : Nat), [254])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [230]), ((1 : Nat), [255])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [231]), ((1 : Nat), [256])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [231]), ((1 : Nat), [257])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [232]), ((1 : Nat), [258])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [232]), ((1 : Nat), [259])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [233]), ((1 : Nat), [260])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [233]), ((1 : Nat), [261])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [234]), ((1 : Nat), [262])]]

def numericExtensionData.leaf2 : List NumericPolynomialChecks.Data :=
  [[((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [234]), ((1 : Nat), [263])],
    [((2013265919 : Nat), []), ((2013265920 : Nat), [1]), ((524288 : Nat), [235]), ((1 : Nat), [264])],
    [((524288 : Nat), []), ((2013265920 : Nat), [2]), ((2013265920 : Nat), [235]), ((1 : Nat), [265])]]

def numericExtensionData : List NumericPolynomialChecks.Data :=
  List.append numericExtensionData.leaf0 (List.append numericExtensionData.leaf1 numericExtensionData.leaf2)

def numericExtensionData.tree : NumericPolynomialChecks.LookupTable NumericPolynomialChecks.Data :=
  NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericExtensionData.leaf0)
    (NumericPolynomialChecks.LookupTable.branch 16
      (NumericPolynomialChecks.LookupTable.leaf numericExtensionData.leaf1)
      (NumericPolynomialChecks.LookupTable.leaf numericExtensionData.leaf2))

theorem numericExtensionData.tree_binding : (numericExtensionData.tree).toList = numericExtensionData := by kernel_rfl

theorem numericExtensionData.tree_valid : (numericExtensionData.tree).valid = true := by kernel_rfl

def numericBackward.leaf0 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 32)], [([((1 : Nat), [])], 33)], [([((1 : Nat), [])], 34)], [([((1 : Nat), [])], 35)],
    [([((1 : Nat), [])], 36)], [([((1 : Nat), [])], 37)], [([((1 : Nat), [])], 38)], [([((1 : Nat), [])], 39)],
    [([((1 : Nat), [])], 40)], [([((1 : Nat), [])], 41)], [([((1 : Nat), [])], 42)], [([((1 : Nat), [])], 43)],
    [([((1 : Nat), [])], 44)], [([((1 : Nat), [])], 45)], [([((1 : Nat), [])], 46)], [([((1 : Nat), [])], 47)]]

def numericBackward.leaf1 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 48)], [([((1 : Nat), [])], 49)], [([((1 : Nat), [])], 50)], [([((1 : Nat), [])], 51)],
    [([((1 : Nat), [])], 52)], [([((1 : Nat), [])], 53)], [([((1 : Nat), [])], 54)], [([((1 : Nat), [])], 55)],
    [([((1 : Nat), [])], 56)], [([((1 : Nat), [])], 57)], [([((1 : Nat), [])], 58)], [([((1 : Nat), [])], 59)],
    [([((1 : Nat), [])], 60)], [([((1 : Nat), [])], 61)], [([((1 : Nat), [])], 62)], [([((1 : Nat), [])], 63)]]

def numericBackward.leaf2 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 51)], [([((1 : Nat), [])], 65)], [([((1 : Nat), [])], 66)], [([((1 : Nat), [])], 67)],
    [([((1 : Nat), [])], 68)], [([((1 : Nat), [])], 69)], [([((1 : Nat), [])], 70)], [([((1 : Nat), [])], 71)],
    [([((1 : Nat), [])], 72)], [([((1 : Nat), [])], 73)], [([((1 : Nat), [])], 74)], [([((1 : Nat), [])], 75)],
    [([((1 : Nat), [])], 76)], [([((1 : Nat), [])], 51)], [([((1 : Nat), [])], 78)], [([((1 : Nat), [])], 79)]]

def numericBackward.leaf3 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 80)], [([((1 : Nat), [])], 81)], [([((1 : Nat), [])], 82)], [([((1 : Nat), [])], 83)],
    [([((1 : Nat), [])], 84)], [([((1 : Nat), [])], 85)], [([((1 : Nat), [])], 86)], [([((1 : Nat), [])], 87)],
    [([((1 : Nat), [])], 88)], [([((1 : Nat), [])], 89)], [([((1 : Nat), [])], 51)], [([((1 : Nat), [])], 91)],
    [([((1 : Nat), [])], 92)], [([((1 : Nat), [])], 93)], [([((1 : Nat), [])], 94)], [([((1 : Nat), [])], 95)]]

def numericBackward.leaf4 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 96)], [([((1 : Nat), [])], 97)], [([((1 : Nat), [])], 98)], [([((1 : Nat), [])], 99)],
    [([((1 : Nat), [])], 100)], [([((1 : Nat), [])], 101)], [([((1 : Nat), [])], 102)], [([((1 : Nat), [])], 51)],
    [([((1 : Nat), [])], 104)], [([((1 : Nat), [])], 105)], [([((1 : Nat), [])], 106)], [([((1 : Nat), [])], 107)],
    [([((1 : Nat), [])], 108)], [([((1 : Nat), [])], 109)], [([((1 : Nat), [])], 110)], [([((1 : Nat), [])], 111)]]

def numericBackward.leaf5 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 112)], [([((1 : Nat), [])], 113)], [([((1 : Nat), [])], 114)], [([((1 : Nat), [])], 115)],
    [([((1 : Nat), [])], 116)], [([((1 : Nat), [])], 117)], [([((1 : Nat), [])], 118)], [([((1 : Nat), [])], 119)],
    [([((1 : Nat), [])], 120)], [([((1 : Nat), [])], 121)], [([((1 : Nat), [])], 122)], [([((1 : Nat), [])], 123)],
    [([((1 : Nat), [])], 124)], [([((1 : Nat), [])], 125)], [([((1 : Nat), [])], 126)], [([((1 : Nat), [])], 127)]]

def numericBackward.leaf6 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 128)], [([((1 : Nat), [])], 129)], [([((1 : Nat), [])], 130)], [([((1 : Nat), [])], 131)],
    [([((1 : Nat), [])], 132)], [([((1 : Nat), [])], 133)], [([((1 : Nat), [])], 134)], [([((1 : Nat), [])], 135)],
    [([((1 : Nat), [])], 136)], [([((1 : Nat), [])], 137)], [([((1 : Nat), [])], 138)], [([((1 : Nat), [])], 139)],
    [([((1 : Nat), [])], 140)], [([((1 : Nat), [])], 141)], [([((1 : Nat), [])], 142)], [([((1 : Nat), [])], 143)]]

def numericBackward.leaf7 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 144)], [([((1 : Nat), [])], 145)], [([((1 : Nat), [])], 146)], [([((1 : Nat), [])], 147)],
    [([((1 : Nat), [])], 148)], [([((1 : Nat), [])], 149)], [([((1 : Nat), [])], 150)], [([((1 : Nat), [])], 151)],
    [([((1 : Nat), [])], 152)], [([((1 : Nat), [])], 153)], [([((1 : Nat), [])], 154)], [([((1 : Nat), [])], 155)],
    [([((1 : Nat), [])], 156)], [([((1 : Nat), [])], 157)], [([((1 : Nat), [])], 158)], [([((1 : Nat), [])], 159)]]

def numericBackward.leaf8 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 160)], [([((1 : Nat), [])], 161)], [([((1 : Nat), [])], 162)], [([((1 : Nat), [])], 163)],
    [([((1 : Nat), [])], 164)], [([((1 : Nat), [])], 165)], [([((1 : Nat), [])], 166)], [([((1 : Nat), [])], 167)],
    [([((1 : Nat), [])], 168)], [([((1 : Nat), [])], 169)], [([((1 : Nat), [])], 170)], [([((1 : Nat), [])], 171)],
    [([((1 : Nat), [])], 172)], [([((1 : Nat), [])], 173)], [([((1 : Nat), [])], 174)], [([((1 : Nat), [])], 175)]]
end Airbender.Compiler.FullArithmeticNative.KeccakCached
