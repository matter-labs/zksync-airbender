import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original184 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 23552 stop 23680
column_blocks_part target184Region6 from Verification.byteShiftColumn6 start 23552 stop 23680
noncomputable def target184 : List Setup.Block := target184Region6

theorem chunkChecked184 : normalizeSetupBlocks original184 = normalizeSetupBlocks target184 := by
  exact congrArg normalizeSetupBlocks (show original184 = target184 from rfl)

theorem chunkLength184 : (original184.map Setup.Block.length).sum = 1206 := by decide +kernel

column_blocks_part original185 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 23680 stop 23808
column_blocks_part target185Region6 from Verification.byteShiftColumn6 start 23680 stop 23808
noncomputable def target185 : List Setup.Block := target185Region6

theorem chunkChecked185 : normalizeSetupBlocks original185 = normalizeSetupBlocks target185 := by
  exact congrArg normalizeSetupBlocks (show original185 = target185 from rfl)

theorem chunkLength185 : (original185.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original186 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 23808 stop 23936
column_blocks_part target186Region6 from Verification.byteShiftColumn6 start 23808 stop 23936
noncomputable def target186 : List Setup.Block := target186Region6

theorem chunkChecked186 : normalizeSetupBlocks original186 = normalizeSetupBlocks target186 := by
  exact congrArg normalizeSetupBlocks (show original186 = target186 from rfl)

theorem chunkLength186 : (original186.map Setup.Block.length).sum = 1226 := by decide +kernel

column_blocks_part original187 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 23936 stop 24064
column_blocks_part target187Region6 from Verification.byteShiftColumn6 start 23936 stop 24064
noncomputable def target187 : List Setup.Block := target187Region6

theorem chunkChecked187 : normalizeSetupBlocks original187 = normalizeSetupBlocks target187 := by
  exact congrArg normalizeSetupBlocks (show original187 = target187 from rfl)

theorem chunkLength187 : (original187.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part original188 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 24064 stop 24192
column_blocks_part target188Region6 from Verification.byteShiftColumn6 start 24064 stop 24192
noncomputable def target188 : List Setup.Block := target188Region6

theorem chunkChecked188 : normalizeSetupBlocks original188 = normalizeSetupBlocks target188 := by
  exact congrArg normalizeSetupBlocks (show original188 = target188 from rfl)

theorem chunkLength188 : (original188.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original189 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 24192 stop 24288
column_blocks_part target189Region6 from Verification.byteShiftColumn6 start 24192 stop 24288
noncomputable def target189 : List Setup.Block := target189Region6

theorem chunkChecked189 : normalizeSetupBlocks original189 = normalizeSetupBlocks target189 := by
  exact congrArg normalizeSetupBlocks (show original189 = target189 from rfl)

theorem chunkLength189 : (original189.map Setup.Block.length).sum = 908 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
