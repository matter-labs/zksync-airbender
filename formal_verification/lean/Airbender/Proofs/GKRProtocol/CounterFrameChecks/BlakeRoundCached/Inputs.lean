import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.TableNative.BlakeRoundCached

namespace Airbender.Compiler.CounterFrameNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/blake-round-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  table_model Airbender.Compiler.TableNative.BlakeRoundCached.native
  helper_model Airbender.Compiler.HelperNative.BlakeRoundCached.native inputs 763 phase 0

end Airbender.Compiler.CounterFrameNative.BlakeRoundCached
