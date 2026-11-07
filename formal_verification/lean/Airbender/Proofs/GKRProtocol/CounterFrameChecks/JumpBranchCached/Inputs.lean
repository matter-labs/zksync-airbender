import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.TableNative.JumpBranchCached

namespace Airbender.Compiler.CounterFrameNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/jump-branch-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  table_model Airbender.Compiler.TableNative.JumpBranchCached.native
  helper_model Airbender.Compiler.HelperNative.JumpBranchCached.native inputs 55 phase 0

end Airbender.Compiler.CounterFrameNative.JumpBranchCached
