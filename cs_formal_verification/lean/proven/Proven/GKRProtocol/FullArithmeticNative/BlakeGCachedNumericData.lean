module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.BlakeGCachedFoundation
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeGCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

open NumericPolynomialChecks

numeric_polynomials numericSource from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["source"]
numeric_polynomials numericNormalizedSource from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["sourceNormalized"]
numeric_polynomials numericLowered from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["lowered"]
numeric_polynomials numericExtensionData from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["extension"]
numeric_polynomials numericGateInputs from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["gateInputNormalized"]
numeric_polynomials numericGateOutputs from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["gateOutputNormalized"]
numeric_combinations numericBackward from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["backward"]
numeric_combinations numericForward from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["forward"]
numeric_naturals numericKeys from "artifacts/compiler/numeric-arithmetic/blake-g-cached.json" ["keys"]

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


end Airbender.Compiler.FullArithmeticNative.BlakeGCached
