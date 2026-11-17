module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.NativeProductImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.ProductNative.KeccakThetaRhoCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/keccak-theta-rho-cached.json"

end Airbender.Compiler.ProductNative.KeccakThetaRhoCached
