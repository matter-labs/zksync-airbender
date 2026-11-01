import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.TableNative.BlakeRoundUncached

namespace Airbender.Compiler.CounterFrameNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/blake-round-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  table_model Airbender.Compiler.TableNative.BlakeRoundUncached.native
  helper_model Airbender.Compiler.HelperNative.BlakeRoundUncached.native inputs 763 phase 0

end Airbender.Compiler.CounterFrameNative.BlakeRoundUncached
