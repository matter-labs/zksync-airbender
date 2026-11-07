import Airbender.Import.GKRProtocol.NativeProductImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.KeccakCached

namespace Airbender.Compiler.ProductNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/keccak-cached.json"

end Airbender.Compiler.ProductNative.KeccakCached
