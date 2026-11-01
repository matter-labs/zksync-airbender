import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.TableNative.UnifiedUncached

namespace Airbender.Compiler.CounterFrameNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/unified-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  table_model Airbender.Compiler.TableNative.UnifiedUncached.native
  helper_model Airbender.Compiler.HelperNative.UnifiedUncached.native inputs 137 phase 0

end Airbender.Compiler.CounterFrameNative.UnifiedUncached
