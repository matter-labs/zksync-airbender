import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.TableNative.MulDivUncached

namespace Airbender.Compiler.CounterFrameNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/mul-div-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  table_model Airbender.Compiler.TableNative.MulDivUncached.native
  helper_model Airbender.Compiler.HelperNative.MulDivUncached.native inputs 71 phase 0

end Airbender.Compiler.CounterFrameNative.MulDivUncached
