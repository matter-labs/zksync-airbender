import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Data.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original136 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 17408 stop 17536
column_blocks_part target136Region6 from Verification.byteShiftColumn5 start 17408 stop 17536
noncomputable def target136 : List Setup.Block := target136Region6

theorem chunkChecked136 : normalizeSetupBlocks original136 = normalizeSetupBlocks target136 := by
  exact congrArg normalizeSetupBlocks (show original136 = target136 from rfl)

theorem chunkLength136 : (original136.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part original137 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 17536 stop 17664
column_blocks_part target137Region6 from Verification.byteShiftColumn5 start 17536 stop 17664
noncomputable def target137 : List Setup.Block := target137Region6

theorem chunkChecked137 : normalizeSetupBlocks original137 = normalizeSetupBlocks target137 := by
  exact congrArg normalizeSetupBlocks (show original137 = target137 from rfl)

theorem chunkLength137 : (original137.map Setup.Block.length).sum = 1176 := by decide +kernel

column_blocks_part original138 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 17664 stop 17792
column_blocks_part target138Region6 from Verification.byteShiftColumn5 start 17664 stop 17792
noncomputable def target138 : List Setup.Block := target138Region6

theorem chunkChecked138 : normalizeSetupBlocks original138 = normalizeSetupBlocks target138 := by
  exact congrArg normalizeSetupBlocks (show original138 = target138 from rfl)

theorem chunkLength138 : (original138.map Setup.Block.length).sum = 1616 := by decide +kernel

column_blocks_part original139 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 17792 stop 17920
column_blocks_part target139Region6 from Verification.byteShiftColumn5 start 17792 stop 17920
noncomputable def target139 : List Setup.Block := target139Region6

theorem chunkChecked139 : normalizeSetupBlocks original139 = normalizeSetupBlocks target139 := by
  exact congrArg normalizeSetupBlocks (show original139 = target139 from rfl)

theorem chunkLength139 : (original139.map Setup.Block.length).sum = 1792 := by decide +kernel

column_blocks_part original140 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 17920 stop 18048
column_blocks_part target140Region6 from Verification.byteShiftColumn5 start 17920 stop 18048
noncomputable def target140 : List Setup.Block := target140Region6

theorem chunkChecked140 : normalizeSetupBlocks original140 = normalizeSetupBlocks target140 := by
  exact congrArg normalizeSetupBlocks (show original140 = target140 from rfl)

theorem chunkLength140 : (original140.map Setup.Block.length).sum = 1576 := by decide +kernel

column_blocks_part original141 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 18048 stop 18176
column_blocks_part target141Region6 from Verification.byteShiftColumn5 start 18048 stop 18176
noncomputable def target141 : List Setup.Block := target141Region6

theorem chunkChecked141 : normalizeSetupBlocks original141 = normalizeSetupBlocks target141 := by
  exact congrArg normalizeSetupBlocks (show original141 = target141 from rfl)

theorem chunkLength141 : (original141.map Setup.Block.length).sum = 1504 := by decide +kernel

column_blocks_part original142 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 18176 stop 18304
column_blocks_part target142Region6 from Verification.byteShiftColumn5 start 18176 stop 18304
noncomputable def target142 : List Setup.Block := target142Region6

theorem chunkChecked142 : normalizeSetupBlocks original142 = normalizeSetupBlocks target142 := by
  exact congrArg normalizeSetupBlocks (show original142 = target142 from rfl)

theorem chunkLength142 : (original142.map Setup.Block.length).sum = 1520 := by decide +kernel

column_blocks_part original143 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 18304 stop 18432
column_blocks_part target143Region6 from Verification.byteShiftColumn5 start 18304 stop 18432
noncomputable def target143 : List Setup.Block := target143Region6

theorem chunkChecked143 : normalizeSetupBlocks original143 = normalizeSetupBlocks target143 := by
  exact congrArg normalizeSetupBlocks (show original143 = target143 from rfl)

theorem chunkLength143 : (original143.map Setup.Block.length).sum = 1352 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column5
