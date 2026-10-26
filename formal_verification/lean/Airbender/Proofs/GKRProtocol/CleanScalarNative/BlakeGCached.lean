import Airbender.Import.GKRProtocol.CleanScalarImport
import Airbender.Proofs.GKRProtocol.MaterializedNative.BlakeGCached

namespace Airbender.Compiler.CleanScalarNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_clean_scalar_setup native model Airbender.Compiler.MaterializedNative.BlakeGCached.native.model

end Airbender.Compiler.CleanScalarNative.BlakeGCached
