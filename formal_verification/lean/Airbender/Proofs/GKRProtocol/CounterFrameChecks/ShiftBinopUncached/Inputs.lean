import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.TableNative.ShiftBinopUncached

namespace Airbender.Compiler.CounterFrameNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/shift-binop-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  table_model Airbender.Compiler.TableNative.ShiftBinopUncached.native
  helper_model Airbender.Compiler.HelperNative.ShiftBinopUncached.native inputs 98 phase 0

end Airbender.Compiler.CounterFrameNative.ShiftBinopUncached
