module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRCompiler.Import

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerArithmetic.KeccakThetaRho
set_option maxRecDepth 32768

import_compiler_arithmetic native from "artifacts/compiler/keccak-theta-rho-cached.json"
  certificate "artifacts/compiler/description-arithmetic/keccak-theta-rho-cached.json" source_description
  only "data" 0 0

end Airbender.Compiler.WorkerArithmetic.KeccakThetaRho
