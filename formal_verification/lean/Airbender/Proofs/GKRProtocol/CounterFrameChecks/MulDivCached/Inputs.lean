import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.MulDivCached
import Airbender.Proofs.GKRProtocol.TableNative.MulDivCached

namespace Airbender.Compiler.CounterFrameNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/mul-div-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  table_model Airbender.Compiler.TableNative.MulDivCached.native
  helper_model Airbender.Compiler.HelperNative.MulDivCached.native inputs 71 phase 0

end Airbender.Compiler.CounterFrameNative.MulDivCached
