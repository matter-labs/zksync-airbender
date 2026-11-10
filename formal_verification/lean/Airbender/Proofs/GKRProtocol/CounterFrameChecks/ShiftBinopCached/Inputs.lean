import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.TableNative.ShiftBinopCached

namespace Airbender.Compiler.CounterFrameNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/shift-binop-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  table_model Airbender.Compiler.TableNative.ShiftBinopCached.native
  helper_model Airbender.Compiler.HelperNative.ShiftBinopCached.native inputs 98 phase 0

end Airbender.Compiler.CounterFrameNative.ShiftBinopCached
