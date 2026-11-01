import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.BigintCached
import Airbender.Proofs.GKRProtocol.TableNative.BigintCached

namespace Airbender.Compiler.CounterFrameNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/bigint-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  table_model Airbender.Compiler.TableNative.BigintCached.native
  helper_model Airbender.Compiler.HelperNative.BigintCached.native inputs 276 phase 0

end Airbender.Compiler.CounterFrameNative.BigintCached
