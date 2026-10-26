import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original128 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 16384 stop 16512
column_blocks_part target128Region6 from Verification.byteShiftColumn6 start 16384 stop 16512
noncomputable def target128 : List Setup.Block := target128Region6

theorem chunkChecked128 : normalizeSetupBlocks original128 = normalizeSetupBlocks target128 := by
  exact congrArg normalizeSetupBlocks (show original128 = target128 from rfl)

theorem chunkLength128 : (original128.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original129 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 16512 stop 16640
column_blocks_part target129Region6 from Verification.byteShiftColumn6 start 16512 stop 16640
noncomputable def target129 : List Setup.Block := target129Region6

theorem chunkChecked129 : normalizeSetupBlocks original129 = normalizeSetupBlocks target129 := by
  exact congrArg normalizeSetupBlocks (show original129 = target129 from rfl)

theorem chunkLength129 : (original129.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original130 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 16640 stop 16768
column_blocks_part target130Region6 from Verification.byteShiftColumn6 start 16640 stop 16768
noncomputable def target130 : List Setup.Block := target130Region6

theorem chunkChecked130 : normalizeSetupBlocks original130 = normalizeSetupBlocks target130 := by
  exact congrArg normalizeSetupBlocks (show original130 = target130 from rfl)

theorem chunkLength130 : (original130.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original131 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 16768 stop 16896
column_blocks_part target131Region6 from Verification.byteShiftColumn6 start 16768 stop 16896
noncomputable def target131 : List Setup.Block := target131Region6

theorem chunkChecked131 : normalizeSetupBlocks original131 = normalizeSetupBlocks target131 := by
  exact congrArg normalizeSetupBlocks (show original131 = target131 from rfl)

theorem chunkLength131 : (original131.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original132 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 16896 stop 17024
column_blocks_part target132Region6 from Verification.byteShiftColumn6 start 16896 stop 17024
noncomputable def target132 : List Setup.Block := target132Region6

theorem chunkChecked132 : normalizeSetupBlocks original132 = normalizeSetupBlocks target132 := by
  exact congrArg normalizeSetupBlocks (show original132 = target132 from rfl)

theorem chunkLength132 : (original132.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original133 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 17024 stop 17152
column_blocks_part target133Region6 from Verification.byteShiftColumn6 start 17024 stop 17152
noncomputable def target133 : List Setup.Block := target133Region6

theorem chunkChecked133 : normalizeSetupBlocks original133 = normalizeSetupBlocks target133 := by
  exact congrArg normalizeSetupBlocks (show original133 = target133 from rfl)

theorem chunkLength133 : (original133.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original134 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 17152 stop 17280
column_blocks_part target134Region6 from Verification.byteShiftColumn6 start 17152 stop 17280
noncomputable def target134 : List Setup.Block := target134Region6

theorem chunkChecked134 : normalizeSetupBlocks original134 = normalizeSetupBlocks target134 := by
  exact congrArg normalizeSetupBlocks (show original134 = target134 from rfl)

theorem chunkLength134 : (original134.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original135 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 17280 stop 17408
column_blocks_part target135Region6 from Verification.byteShiftColumn6 start 17280 stop 17408
noncomputable def target135 : List Setup.Block := target135Region6

theorem chunkChecked135 : normalizeSetupBlocks original135 = normalizeSetupBlocks target135 := by
  exact congrArg normalizeSetupBlocks (show original135 = target135 from rfl)

theorem chunkLength135 : (original135.map Setup.Block.length).sum = 2048 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
