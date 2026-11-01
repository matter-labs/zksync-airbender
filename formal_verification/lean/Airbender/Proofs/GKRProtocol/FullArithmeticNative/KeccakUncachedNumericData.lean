import Airbender.Proofs.GKRProtocol.FullArithmeticNative.KeccakUncachedFoundation
import Airbender.Import.GKRProtocol.NumericExpressionDataImport
import Airbender.Proofs.GKRProtocol.FastNumericNormalization

namespace Airbender.Compiler.FullArithmeticNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

open NumericPolynomialChecks

numeric_polynomials numericSource from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["source"]
numeric_polynomials numericLowered from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["lowered"]
numeric_polynomials numericExtensionData from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["extension"]
numeric_combinations numericBackward from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["backward"]
numeric_combinations numericForward from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["forward"]
numeric_naturals numericKeys from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["keys"]

numeric_data_binding numericLowered_binding :
  native.artifact.translation.lowered.map encode = numericLowered
numeric_data_binding numericExtensionData_binding :
  native.extensionData.toList.map encode = numericExtensionData
numeric_data_binding numericBackward_binding :
  native.backwardData.toList.map encodeCombination = numericBackward
numeric_data_binding numericForward_binding :
  native.forwardData.toList.map encodeCombination = numericForward
numeric_polynomials numericSourceHelpers from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["sourceHelpers"]
numeric_expressions numericSourceExpressions from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["sourceExpressions"]
def originalSourceExpressions : List (Expression 266 Source.BaseField) := [native.originalExpression0, native.originalExpression1, native.originalExpression2, native.originalExpression3, native.originalExpression4, native.originalExpression5, native.originalExpression6, native.originalExpression7, native.originalExpression8, native.originalExpression9, native.originalExpression10, native.originalExpression11, native.originalExpression12, native.originalExpression13, native.originalExpression14, native.originalExpression15, native.originalExpression16, native.originalExpression17, native.originalExpression18, native.originalExpression19, native.originalExpression20, native.originalExpression21, native.originalExpression22, native.originalExpression23, native.originalExpression24, native.originalExpression25, native.originalExpression26, native.originalExpression27, native.originalExpression28, native.originalExpression29, native.originalExpression30, native.originalExpression31, native.originalExpression32, native.originalExpression33, native.originalExpression34, native.originalExpression35, native.originalExpression36, native.originalExpression37, native.originalExpression38, native.originalExpression39, native.originalExpression40, native.originalExpression41, native.originalExpression42, native.originalExpression43, native.originalExpression44, native.originalExpression45, native.originalExpression46, native.originalExpression47, native.originalExpression48, native.originalExpression49, native.originalExpression50, native.originalExpression51, native.originalExpression52, native.originalExpression53, native.originalExpression54, native.originalExpression55, native.originalExpression56, native.originalExpression57, native.originalExpression58, native.originalExpression59, native.originalExpression60, native.originalExpression61, native.originalExpression62, native.originalExpression63, native.originalExpression64, native.originalExpression65, native.originalExpression66, native.originalExpression67, native.originalExpression68, native.originalExpression69, native.originalExpression70, native.originalExpression71, native.originalExpression72, native.originalExpression73, native.originalExpression74, native.originalExpression75, native.originalExpression76, native.originalExpression77, native.originalExpression78, native.originalExpression79, native.originalExpression80, native.originalExpression81, native.originalExpression82, native.originalExpression83, native.originalExpression84, native.originalExpression85, native.originalExpression86, native.originalExpression87, native.originalExpression88, native.originalExpression89, native.originalExpression90, native.originalExpression91, native.originalExpression92, native.originalExpression93, native.originalExpression94, native.originalExpression95, native.originalExpression96, native.originalExpression97, native.originalExpression98, native.originalExpression99, native.originalExpression100, native.originalExpression101, native.originalExpression102, native.originalExpression103, native.originalExpression104, native.originalExpression105, native.originalExpression106, native.originalExpression107, native.originalExpression108, native.originalExpression109, native.originalExpression110, native.originalExpression111, native.originalExpression112, native.originalExpression113, native.originalExpression114, native.originalExpression115, native.originalExpression116, native.originalExpression117, native.originalExpression118, native.originalExpression119, native.originalExpression120, native.originalExpression121, native.originalExpression122, native.originalExpression123, native.originalExpression124, native.originalExpression125, native.originalExpression126, native.originalExpression127, native.originalExpression128, native.originalExpression129, native.originalExpression130, native.originalExpression131, native.originalExpression132, native.originalExpression133, native.originalExpression134, native.originalExpression135, native.originalExpression136, native.originalExpression137, native.originalExpression138, native.originalExpression139, native.originalExpression140, native.originalExpression141, native.originalExpression142, native.originalExpression143, native.originalExpression144, native.originalExpression145, native.originalExpression146, native.originalExpression147, native.originalExpression148, native.originalExpression149, native.originalExpression150, native.originalExpression151, native.originalExpression152, native.originalExpression153, native.originalExpression154, native.originalExpression155, native.originalExpression156, native.originalExpression157, native.originalExpression158, native.originalExpression159, native.originalExpression160, native.originalExpression161, native.originalExpression162, native.originalExpression163, native.originalExpression164, native.originalExpression165, native.originalExpression166, native.originalExpression167, native.originalExpression168, native.originalExpression169, native.originalExpression170, native.originalExpression171, native.originalExpression172]

numeric_data_binding sourceExpressionLayout : native.artifact.source =
  originalSourceExpressions.map Expression.polynomial ++
    native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement)
numeric_data_binding numericSourceExpressions_binding :
  originalSourceExpressions.map NumericExpressionChecks.encode = numericSourceExpressions
numeric_data_binding numericSourceHelpers_binding :
  (native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement)).map encode = numericSourceHelpers
numeric_data_binding numericSourceExpansion_binding :
  numericSourceExpressions.map (NumericExpressionChecks.Code.polynomial babyBearModulus) ++ numericSourceHelpers = numericSource
theorem numericSource_binding : native.artifact.source.map encode = numericSource :=
  (congrArg (List.map encode) sourceExpressionLayout).trans
    (NumericExpressionChecks.source_binding originalSourceExpressions
      (native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement))
      numericSourceExpressions numericSourceHelpers numericSource
      numericSourceExpressions_binding numericSourceHelpers_binding numericSourceExpansion_binding)

numeric_polynomials numericNormalizedSource from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["sourceNormalized"]
numeric_data_binding fastNormalizedSource :
  numericSource.map (FastNormalization.normalize babyBearModulus) = numericNormalizedSource
theorem numericNormalizedSource_binding : numericSource.map (NumericPolynomialChecks.normalize babyBearModulus) = numericNormalizedSource :=
  (FastNormalization.map_eq babyBearModulus numericSource).symm.trans fastNormalizedSource
numeric_polynomials numericRawGateInputs from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["gateInput"]
numeric_data_binding numericRawGateInputs_binding : native.artifact.gates.map (fun gate => encode (NumericArithmeticChecks.gateInput gate)) = numericRawGateInputs

numeric_polynomials numericGateInputs from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["gateInputNormalized"]
numeric_data_binding fastGateInputs : numericRawGateInputs.map (FastNormalization.normalize babyBearModulus) = numericGateInputs
theorem numericRawGateInputs_normalization : numericRawGateInputs.map (NumericPolynomialChecks.normalize babyBearModulus) = numericGateInputs :=
  (FastNormalization.map_eq babyBearModulus numericRawGateInputs).symm.trans fastGateInputs
numeric_polynomials numericRawGateOutputs from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["gateOutput"]
numeric_data_binding numericRawGateOutputs_binding : native.artifact.gates.map (fun gate => encode (NumericArithmeticChecks.gateOutput gate)) = numericRawGateOutputs

numeric_polynomials numericGateOutputs from "artifacts/compiler/numeric-arithmetic/keccak-uncached.json" ["gateOutputNormalized"]
numeric_data_binding fastGateOutputs : numericRawGateOutputs.map (FastNormalization.normalize babyBearModulus) = numericGateOutputs
theorem numericRawGateOutputs_normalization : numericRawGateOutputs.map (NumericPolynomialChecks.normalize babyBearModulus) = numericGateOutputs :=
  (FastNormalization.map_eq babyBearModulus numericRawGateOutputs).symm.trans fastGateOutputs




end Airbender.Compiler.FullArithmeticNative.KeccakUncached
