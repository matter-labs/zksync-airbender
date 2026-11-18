module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRCompiler.Import

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerArithmetic.KeccakChi5
set_option maxRecDepth 32768

import_compiler_arithmetic native from "artifacts/compiler/keccak-chi5-cached.json"
  certificate "artifacts/compiler/description-arithmetic/keccak-chi5-cached.json" source_description

end Airbender.Compiler.WorkerArithmetic.KeccakChi5
