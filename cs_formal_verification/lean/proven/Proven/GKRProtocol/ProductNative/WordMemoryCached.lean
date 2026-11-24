module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.NativeProductImport
public import Proven.GKRProtocol.ConsumerNative.WordMemoryCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.ProductNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/word-memory-cached.json"

end Airbender.Compiler.ProductNative.WordMemoryCached
