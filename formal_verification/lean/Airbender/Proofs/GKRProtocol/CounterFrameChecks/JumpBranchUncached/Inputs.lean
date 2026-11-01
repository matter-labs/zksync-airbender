import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.TableNative.JumpBranchUncached

namespace Airbender.Compiler.CounterFrameNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/jump-branch-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  table_model Airbender.Compiler.TableNative.JumpBranchUncached.native
  helper_model Airbender.Compiler.HelperNative.JumpBranchUncached.native inputs 55 phase 0

end Airbender.Compiler.CounterFrameNative.JumpBranchUncached
