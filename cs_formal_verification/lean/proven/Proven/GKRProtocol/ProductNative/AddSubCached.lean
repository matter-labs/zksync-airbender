module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.NativeProductImport
public import Proven.GKRProtocol.ConsumerNative.AddSubCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.ProductNative.AddSubCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/add-sub-cached.json"

end Airbender.Compiler.ProductNative.AddSubCached
