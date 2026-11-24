module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part003
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part008
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part019
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part022
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part024
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part027
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part030
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part031
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part032
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

def numericGateOutputs.leaf11 : List NumericPolynomialChecks.Data :=
  [[((1 : Nat), [39, 69]), ((2013265920 : Nat), [41, 69])], [((1 : Nat), [40, 69]), ((2013265920 : Nat), [42, 69])],
    [((1 : Nat), [43, 69]), ((2013265920 : Nat), [45, 69])],
    [((1 : Nat), [44, 69]), ((2013265920 : Nat), [46, 69])],
    [((1 : Nat), [47, 69]), ((2013265920 : Nat), [49, 69])],
    [((1 : Nat), [48, 69]), ((2013265920 : Nat), [50, 69])],
    [((1 : Nat), [51, 69]), ((2013265920 : Nat), [53, 69])],
    [((1 : Nat), [52, 69]), ((2013265920 : Nat), [54, 69])],
    [((1 : Nat), [55, 69]), ((2013265920 : Nat), [57, 69])],
    [((1 : Nat), [56, 69]), ((2013265920 : Nat), [58, 69])],
    [((1 : Nat), [59, 69]), ((2013265920 : Nat), [61, 69])],
    [((1 : Nat), [60, 69]), ((2013265920 : Nat), [62, 69])], [((2013265920 : Nat), [63]), ((1 : Nat), [63, 63])],
    [((2013265920 : Nat), [64]), ((1 : Nat), [64, 64])], [((2013265920 : Nat), [65]), ((1 : Nat), [65, 65])],
    [((2013265920 : Nat), [66]), ((1 : Nat), [66, 66])]]

def numericGateOutputs.leaf12 : List NumericPolynomialChecks.Data :=
  [[((2013265920 : Nat), [67]), ((1 : Nat), [67, 67])], [((2013265920 : Nat), [68]), ((1 : Nat), [68, 68])],
    [((2013265920 : Nat), [69]), ((1 : Nat), [69, 69])], [((2013265920 : Nat), [70]), ((1 : Nat), [70, 70])],
    [((2013265920 : Nat), [71]), ((1 : Nat), [71, 71])], [((2013265920 : Nat), [72]), ((1 : Nat), [72, 72])],
    [((2013265920 : Nat), [73]), ((1 : Nat), [73, 73])], [((2013265920 : Nat), [74]), ((1 : Nat), [74, 74])],
    [((2013265920 : Nat), [75]), ((1 : Nat), [75, 75])], [((2013265920 : Nat), [76]), ((1 : Nat), [76, 76])],
    [((2013265920 : Nat), [77]), ((1 : Nat), [77, 77])], [((2013265920 : Nat), [78]), ((1 : Nat), [78, 78])],
    [((2013265920 : Nat), [79]), ((1 : Nat), [79, 79])], [((2013265920 : Nat), [222]), ((1 : Nat), [222, 222])],
    [((2013265920 : Nat), [223]), ((1 : Nat), [223, 223])], [((2013265920 : Nat), [224]), ((1 : Nat), [224, 224])]]

def numericGateOutputs.leaf13 : List NumericPolynomialChecks.Data :=
  [[((2013265920 : Nat), [225]), ((1 : Nat), [225, 225])], [((2013265920 : Nat), [226]), ((1 : Nat), [226, 226])],
    [((2013265920 : Nat), [227]), ((1 : Nat), [227, 227])], [((2013265920 : Nat), [228]), ((1 : Nat), [228, 228])],
    [((2013265920 : Nat), [229]), ((1 : Nat), [229, 229])], [((2013265920 : Nat), [230]), ((1 : Nat), [230, 230])],
    [((2013265920 : Nat), [231]), ((1 : Nat), [231, 231])], [((2013265920 : Nat), [232]), ((1 : Nat), [232, 232])],
    [((2013265920 : Nat), [233]), ((1 : Nat), [233, 233])], [((2013265920 : Nat), [234]), ((1 : Nat), [234, 234])],
    [((2013265920 : Nat), [235]), ((1 : Nat), [235, 235])], [], [], []]

def numericGateOutputs : List NumericPolynomialChecks.Data :=
  List.append
    (List.append
      (List.append numericGateOutputs.leaf0 (List.append numericGateOutputs.leaf1 numericGateOutputs.leaf2))
      (List.append (List.append numericGateOutputs.leaf3 numericGateOutputs.leaf4)
        (List.append numericGateOutputs.leaf5 numericGateOutputs.leaf6)))
    (List.append
      (List.append numericGateOutputs.leaf7 (List.append numericGateOutputs.leaf8 numericGateOutputs.leaf9))
      (List.append (List.append numericGateOutputs.leaf10 numericGateOutputs.leaf11)
        (List.append numericGateOutputs.leaf12 numericGateOutputs.leaf13)))

def numericGateOutputs.tree : NumericPolynomialChecks.LookupTable NumericPolynomialChecks.Data :=
  NumericPolynomialChecks.LookupTable.branch 112
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16
        (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf0)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf1)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf2)))
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf3)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf4))
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf5)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf6))))
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16
        (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf7)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf8)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf9)))
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf10)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf11))
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf12)
          (NumericPolynomialChecks.LookupTable.leaf numericGateOutputs.leaf13))))

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
end Airbender.Compiler.FullArithmeticNative.KeccakCached
