module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.NativeProductImport
public import Proven.GKRProtocol.ConsumerNative.SubwordMemoryCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.ProductNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/subword-memory-cached.json"

end Airbender.Compiler.ProductNative.SubwordMemoryCached
