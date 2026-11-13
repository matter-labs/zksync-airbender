module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.NativeLookupImport
public import Proven.GKRProtocol.ConsumerNative.MulDivCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.LookupNative.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_lookups native from "artifacts/compiler/mul-div-cached.json"

end Airbender.Compiler.LookupNative.MulDivCached
