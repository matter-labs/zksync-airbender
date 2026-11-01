import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.BigintUncached
import Airbender.Proofs.GKRProtocol.TableNative.BigintUncached

namespace Airbender.Compiler.CounterFrameNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/bigint-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  table_model Airbender.Compiler.TableNative.BigintUncached.native
  helper_model Airbender.Compiler.HelperNative.BigintUncached.native inputs 276 phase 0

end Airbender.Compiler.CounterFrameNative.BigintUncached
