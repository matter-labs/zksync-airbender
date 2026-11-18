module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRCompiler.Import

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerArithmetic.KeccakColumnParity
set_option maxRecDepth 32768

import_compiler_arithmetic native from "artifacts/compiler/keccak-column-parity-cached.json"
  certificate "artifacts/compiler/description-arithmetic/keccak-column-parity-cached.json" source_description

end Airbender.Compiler.WorkerArithmetic.KeccakColumnParity
