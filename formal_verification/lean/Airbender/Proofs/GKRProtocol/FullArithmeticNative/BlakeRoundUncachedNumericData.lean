import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeRoundUncachedFoundation
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

open NumericPolynomialChecks

numeric_polynomials numericSource from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["source"]
numeric_polynomials numericNormalizedSource from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["sourceNormalized"]
numeric_polynomials numericLowered from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["lowered"]
numeric_polynomials numericExtensionData from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["extension"]
numeric_polynomials numericGateInputs from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["gateInputNormalized"]
numeric_polynomials numericGateOutputs from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["gateOutputNormalized"]
numeric_combinations numericBackward from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["backward"]
numeric_combinations numericForward from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["forward"]
numeric_naturals numericKeys from "artifacts/compiler/numeric-arithmetic/blake-round-uncached.json" ["keys"]

numeric_data_binding numericSource_binding :
  native.artifact.source.map encode = numericSource
numeric_data_binding numericNormalizedSource_binding :
  numericSource.map (NumericPolynomialChecks.normalize babyBearModulus) = numericNormalizedSource
numeric_data_binding numericLowered_binding :
  native.artifact.translation.lowered.map encode = numericLowered
numeric_data_binding numericExtensionData_binding :
  native.extensionData.toList.map encode = numericExtensionData
numeric_data_binding numericBackward_binding :
  native.backwardData.toList.map encodeCombination = numericBackward
numeric_data_binding numericForward_binding :
  native.forwardData.toList.map encodeCombination = numericForward


end Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached
