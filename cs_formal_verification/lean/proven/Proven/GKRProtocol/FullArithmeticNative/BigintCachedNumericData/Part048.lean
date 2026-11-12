module
public import Proven.KernelRfl
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part003
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part008
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part033
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part034
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part036
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part039
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part041
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part045
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part046
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericData.Part047
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

def numericGateOutputs.leaf7 : List NumericPolynomialChecks.Data :=
  [[((2013235201 : Nat), [34, 54]), ((30720 : Nat), [34, 130]), ((30720 : Nat), [54, 114]),
      ((2013235201 : Nat), [114, 130]), ((30720 : Nat), [161]), ((2013265920 : Nat), [162]),
      ((2013235201 : Nat), [193])],
    [((1 : Nat), [5, 64]), ((2013265920 : Nat), [7]), ((1 : Nat), [59, 67]), ((1 : Nat), [60, 67]),
      ((1 : Nat), [61, 67]), ((1 : Nat), [62, 131]), ((1 : Nat), [63, 147]), ((1 : Nat), [66, 67])],
    [((1 : Nat), [6, 64]), ((2013265920 : Nat), [8]), ((1 : Nat), [59, 68]), ((1 : Nat), [60, 68]),
      ((1 : Nat), [61, 68]), ((1 : Nat), [62, 132]), ((1 : Nat), [63, 148]), ((1 : Nat), [66, 68])],
    [((1 : Nat), [9, 64]), ((2013265920 : Nat), [11]), ((1 : Nat), [59, 69]), ((1 : Nat), [60, 69]),
      ((1 : Nat), [61, 69]), ((1 : Nat), [62, 133]), ((1 : Nat), [63, 149]), ((1 : Nat), [66, 69])],
    [((1 : Nat), [10, 64]), ((2013265920 : Nat), [12]), ((1 : Nat), [59, 70]), ((1 : Nat), [60, 70]),
      ((1 : Nat), [61, 70]), ((1 : Nat), [62, 134]), ((1 : Nat), [63, 150]), ((1 : Nat), [66, 70])],
    [((1 : Nat), [13, 64]), ((2013265920 : Nat), [15]), ((1 : Nat), [59, 71]), ((1 : Nat), [60, 71]),
      ((1 : Nat), [61, 71]), ((1 : Nat), [62, 135]), ((1 : Nat), [63, 151]), ((1 : Nat), [66, 71])],
    [((1 : Nat), [14, 64]), ((2013265920 : Nat), [16]), ((1 : Nat), [59, 72]), ((1 : Nat), [60, 72]),
      ((1 : Nat), [61, 72]), ((1 : Nat), [62, 136]), ((1 : Nat), [63, 152]), ((1 : Nat), [66, 72])],
    [((1 : Nat), [17, 64]), ((2013265920 : Nat), [19]), ((1 : Nat), [59, 73]), ((1 : Nat), [60, 73]),
      ((1 : Nat), [61, 73]), ((1 : Nat), [62, 137]), ((1 : Nat), [63, 153]), ((1 : Nat), [66, 73])],
    [((1 : Nat), [18, 64]), ((2013265920 : Nat), [20]), ((1 : Nat), [59, 74]), ((1 : Nat), [60, 74]),
      ((1 : Nat), [61, 74]), ((1 : Nat), [62, 138]), ((1 : Nat), [63, 154]), ((1 : Nat), [66, 74])],
    [((1 : Nat), [21, 64]), ((2013265920 : Nat), [23]), ((1 : Nat), [59, 75]), ((1 : Nat), [60, 75]),
      ((1 : Nat), [61, 75]), ((1 : Nat), [62, 139]), ((1 : Nat), [63, 155]), ((1 : Nat), [66, 75])],
    [((1 : Nat), [22, 64]), ((2013265920 : Nat), [24]), ((1 : Nat), [59, 76]), ((1 : Nat), [60, 76]),
      ((1 : Nat), [61, 76]), ((1 : Nat), [62, 140]), ((1 : Nat), [63, 156]), ((1 : Nat), [66, 76])],
    [((1 : Nat), [25, 64]), ((2013265920 : Nat), [27]), ((1 : Nat), [59, 77]), ((1 : Nat), [60, 77]),
      ((1 : Nat), [61, 77]), ((1 : Nat), [62, 141]), ((1 : Nat), [63, 157]), ((1 : Nat), [66, 77])],
    [((1 : Nat), [26, 64]), ((2013265920 : Nat), [28]), ((1 : Nat), [59, 78]), ((1 : Nat), [60, 78]),
      ((1 : Nat), [61, 78]), ((1 : Nat), [62, 142]), ((1 : Nat), [63, 158]), ((1 : Nat), [66, 78])],
    [((1 : Nat), [29, 64]), ((2013265920 : Nat), [31]), ((1 : Nat), [59, 79]), ((1 : Nat), [60, 79]),
      ((1 : Nat), [61, 79]), ((1 : Nat), [62, 143]), ((1 : Nat), [63, 159]), ((1 : Nat), [66, 79])],
    [((1 : Nat), [30, 64]), ((2013265920 : Nat), [32]), ((1 : Nat), [59, 80]), ((1 : Nat), [60, 80]),
      ((1 : Nat), [61, 80]), ((1 : Nat), [62, 144]), ((1 : Nat), [63, 160]), ((1 : Nat), [66, 80])],
    [((1 : Nat), [33, 64]), ((2013265920 : Nat), [35]), ((1 : Nat), [59, 81]), ((1 : Nat), [60, 81]),
      ((1 : Nat), [61, 81]), ((1 : Nat), [62, 145]), ((1 : Nat), [63, 161]), ((1 : Nat), [66, 81])]]

def numericGateOutputs.leaf8 : List NumericPolynomialChecks.Data :=
  [[((1 : Nat), [34, 64]), ((2013265920 : Nat), [36]), ((1 : Nat), [59, 82]), ((1 : Nat), [60, 82]),
      ((1 : Nat), [61, 82]), ((1 : Nat), [62, 146]), ((1 : Nat), [63, 162]), ((1 : Nat), [66, 82])],
    [((2013265920 : Nat), [98, 212]), ((1 : Nat), [212]), ((2013265920 : Nat), [215])],
    [((2013265920 : Nat), [57]), ((1 : Nat), [59, 98]), ((1 : Nat), [60, 98]), ((1 : Nat), [61, 98]),
      ((1 : Nat), [62]), ((2013265920 : Nat), [62, 212]), ((1 : Nat), [64, 215]), ((1 : Nat), [66, 98])],
    [((1 : Nat), [58])], [((2013265920 : Nat), [59]), ((1 : Nat), [59, 59])],
    [((2013265920 : Nat), [60]), ((1 : Nat), [60, 60])], [((2013265920 : Nat), [61]), ((1 : Nat), [61, 61])],
    [((2013265920 : Nat), [62]), ((1 : Nat), [62, 62])], [((2013265920 : Nat), [63]), ((1 : Nat), [63, 63])],
    [((2013265920 : Nat), [64]), ((1 : Nat), [64, 64])], [((2013265920 : Nat), [65]), ((1 : Nat), [65, 65])],
    [((2013265920 : Nat), [66]), ((1 : Nat), [66, 66])], [((2013265920 : Nat), [83]), ((1 : Nat), [83, 83])],
    [((2013265920 : Nat), [84]), ((1 : Nat), [84, 84])], [((2013265920 : Nat), [85]), ((1 : Nat), [85, 85])],
    [((2013265920 : Nat), [86]), ((1 : Nat), [86, 86])]]

def numericGateOutputs.leaf9 : List NumericPolynomialChecks.Data :=
  [[((2013265920 : Nat), [87]), ((1 : Nat), [87, 87])], [((2013265920 : Nat), [88]), ((1 : Nat), [88, 88])],
    [((2013265920 : Nat), [89]), ((1 : Nat), [89, 89])], [((2013265920 : Nat), [90]), ((1 : Nat), [90, 90])],
    [((2013265920 : Nat), [91]), ((1 : Nat), [91, 91])], [((2013265920 : Nat), [92]), ((1 : Nat), [92, 92])],
    [((2013265920 : Nat), [93]), ((1 : Nat), [93, 93])], [((2013265920 : Nat), [94]), ((1 : Nat), [94, 94])],
    [((2013265920 : Nat), [95]), ((1 : Nat), [95, 95])], [((2013265920 : Nat), [96]), ((1 : Nat), [96, 96])],
    [((2013265920 : Nat), [97]), ((1 : Nat), [97, 97])], [((2013265920 : Nat), [98]), ((1 : Nat), [98, 98])],
    [((2013265920 : Nat), [212]), ((1 : Nat), [212, 212])], [((2013265920 : Nat), [216]), ((1 : Nat), [216, 216])],
    [((2013265920 : Nat), [217]), ((1 : Nat), [217, 217])], [((2013265920 : Nat), [218]), ((1 : Nat), [218, 218])]]

def numericGateOutputs.leaf10 : List NumericPolynomialChecks.Data :=
  [[((2013265920 : Nat), [219]), ((1 : Nat), [219, 219])], [((2013265920 : Nat), [220]), ((1 : Nat), [220, 220])],
    [((2013265920 : Nat), [221]), ((1 : Nat), [221, 221])], [((2013265920 : Nat), [222]), ((1 : Nat), [222, 222])],
    [((2013265920 : Nat), [223]), ((1 : Nat), [223, 223])], [((2013265920 : Nat), [224]), ((1 : Nat), [224, 224])],
    [((2013265920 : Nat), [225]), ((1 : Nat), [225, 225])], [((2013265920 : Nat), [226]), ((1 : Nat), [226, 226])],
    [((2013265920 : Nat), [227]), ((1 : Nat), [227, 227])], [((2013265920 : Nat), [228]), ((1 : Nat), [228, 228])],
    [((2013265920 : Nat), [229]), ((1 : Nat), [229, 229])], [((2013265920 : Nat), [230]), ((1 : Nat), [230, 230])],
    [((2013265920 : Nat), [231]), ((1 : Nat), [231, 231])], [((2013265920 : Nat), [232]), ((1 : Nat), [232, 232])],
    [((2013265920 : Nat), [233]), ((1 : Nat), [233, 233])], [((2013265920 : Nat), [234]), ((1 : Nat), [234, 234])]]

def numericGateOutputs.leaf11 : List NumericPolynomialChecks.Data :=
  [[], [((1 : Nat), [210, 214])], [((2013265920 : Nat), []), ((1 : Nat), [210, 213]), ((1 : Nat), [214])], [], [],
    []]

def numericGateOutputs : List NumericPolynomialChecks.Data :=
  List.append
    (List.append
      (List.append numericGateOutputs.leaf0 (List.append numericGateOutputs.leaf1 numericGateOutputs.leaf2))
      (List.append numericGateOutputs.leaf3 (List.append numericGateOutputs.leaf4 numericGateOutputs.leaf5)))
    (List.append
      (List.append numericGateOutputs.leaf6 (List.append numericGateOutputs.leaf7 numericGateOutputs.leaf8))
      (List.append numericGateOutputs.leaf9 (List.append numericGateOutputs.leaf10 numericGateOutputs.leaf11)))

def numericGateOutputs.tree : NumericPolynomialChecks.LookupTable NumericPolynomialChecks.Data :=
  NumericPolynomialChecks.LookupTable.branch 96
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16
        (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf0)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf1)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf2)))
      (NumericPolynomialChecks.LookupTable.branch 16
        (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf3)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf4)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf5))))
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16
        (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf6)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf7)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf8)))
      (NumericPolynomialChecks.LookupTable.branch 16
        (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf9)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf10)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf11))))

theorem numericGateOutputs.tree_binding : (numericGateOutputs.tree).toList = numericGateOutputs := by kernel_rfl

theorem numericGateOutputs.tree_valid : (numericGateOutputs.tree).valid = true := by kernel_rfl

theorem fastGateOutputs :
    numericRawGateOutputs.map (FastNormalization.normalize babyBearModulus) = numericGateOutputs := by kernel_rfl

theorem numericSource_binding : native.artifact.source.map encode = numericSource :=
  (congrArg (List.map encode) sourceExpressionLayout).trans
    (NumericExpressionChecks.source_binding originalSourceExpressions
      (native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement))
      numericSourceExpressions numericSourceHelpers numericSource
      numericSourceExpressions_binding numericSourceHelpers_binding numericSourceExpansion_binding)

theorem numericNormalizedSource_binding : numericSource.map (NumericPolynomialChecks.normalize babyBearModulus) = numericNormalizedSource :=
  (FastNormalization.map_eq babyBearModulus numericSource).symm.trans fastNormalizedSource

theorem numericRawGateInputs_normalization : numericRawGateInputs.map (NumericPolynomialChecks.normalize babyBearModulus) = numericGateInputs :=
  (FastNormalization.map_eq babyBearModulus numericRawGateInputs).symm.trans fastGateInputs

theorem numericRawGateOutputs_normalization : numericRawGateOutputs.map (NumericPolynomialChecks.normalize babyBearModulus) = numericGateOutputs :=
  (FastNormalization.map_eq babyBearModulus numericRawGateOutputs).symm.trans fastGateOutputs
end Airbender.Compiler.FullArithmeticNative.BigintCached
