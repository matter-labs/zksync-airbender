import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original152 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 19456 stop 19584
column_blocks_part target152Region6 from Verification.byteShiftColumn4 start 19456 stop 19584
noncomputable def target152 : List Setup.Block := target152Region6

theorem chunkChecked152 : normalizeSetupBlocks original152 = normalizeSetupBlocks target152 := by
  exact congrArg normalizeSetupBlocks (show original152 = target152 from rfl)

theorem chunkLength152 : (original152.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original153 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 19584 stop 19712
column_blocks_part target153Region6 from Verification.byteShiftColumn4 start 19584 stop 19712
noncomputable def target153 : List Setup.Block := target153Region6

theorem chunkChecked153 : normalizeSetupBlocks original153 = normalizeSetupBlocks target153 := by
  exact congrArg normalizeSetupBlocks (show original153 = target153 from rfl)

theorem chunkLength153 : (original153.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original154 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 19712 stop 19840
column_blocks_part target154Region6 from Verification.byteShiftColumn4 start 19712 stop 19840
noncomputable def target154 : List Setup.Block := target154Region6

theorem chunkChecked154 : normalizeSetupBlocks original154 = normalizeSetupBlocks target154 := by
  exact congrArg normalizeSetupBlocks (show original154 = target154 from rfl)

theorem chunkLength154 : (original154.map Setup.Block.length).sum = 1090 := by decide +kernel

column_blocks_part original155 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 19840 stop 19968
column_blocks_part target155Region6 from Verification.byteShiftColumn4 start 19840 stop 19968
noncomputable def target155 : List Setup.Block := target155Region6

theorem chunkChecked155 : normalizeSetupBlocks original155 = normalizeSetupBlocks target155 := by
  exact congrArg normalizeSetupBlocks (show original155 = target155 from rfl)

theorem chunkLength155 : (original155.map Setup.Block.length).sum = 1222 := by decide +kernel

column_blocks_part original156 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 19968 stop 20096
column_blocks_part target156Region6 from Verification.byteShiftColumn4 start 19968 stop 20096
noncomputable def target156 : List Setup.Block := target156Region6

theorem chunkChecked156 : normalizeSetupBlocks original156 = normalizeSetupBlocks target156 := by
  exact congrArg normalizeSetupBlocks (show original156 = target156 from rfl)

theorem chunkLength156 : (original156.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part original157 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 20096 stop 20224
column_blocks_part target157Region6 from Verification.byteShiftColumn4 start 20096 stop 20224
noncomputable def target157 : List Setup.Block := target157Region6

theorem chunkChecked157 : normalizeSetupBlocks original157 = normalizeSetupBlocks target157 := by
  exact congrArg normalizeSetupBlocks (show original157 = target157 from rfl)

theorem chunkLength157 : (original157.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part original158 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 20224 stop 20352
column_blocks_part target158Region6 from Verification.byteShiftColumn4 start 20224 stop 20352
noncomputable def target158 : List Setup.Block := target158Region6

theorem chunkChecked158 : normalizeSetupBlocks original158 = normalizeSetupBlocks target158 := by
  exact congrArg normalizeSetupBlocks (show original158 = target158 from rfl)

theorem chunkLength158 : (original158.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original159 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 20352 stop 20480
column_blocks_part target159Region6 from Verification.byteShiftColumn4 start 20352 stop 20480
noncomputable def target159 : List Setup.Block := target159Region6

theorem chunkChecked159 : normalizeSetupBlocks original159 = normalizeSetupBlocks target159 := by
  exact congrArg normalizeSetupBlocks (show original159 = target159 from rfl)

theorem chunkLength159 : (original159.map Setup.Block.length).sum = 1080 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column4
