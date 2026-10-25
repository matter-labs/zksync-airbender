import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original192 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 24576 stop 24671
column_blocks_part target192Region6 from Verification.byteShiftColumn7 start 24576 stop 24671
noncomputable def target192 : List Setup.Block := target192Region6

theorem chunkChecked192 : normalizeSetupBlocks original192 = normalizeSetupBlocks target192 := by
  exact congrArg normalizeSetupBlocks (show original192 = target192 from rfl)

theorem chunkLength192 : (original192.map Setup.Block.length).sum = 1484 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column7
