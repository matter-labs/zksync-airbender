import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Data.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original40 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 5120 stop 5248
column_blocks_part target40Region6 from Verification.byteShiftColumn4 start 5120 stop 5248
noncomputable def target40 : List Setup.Block := target40Region6

theorem chunkChecked40 : normalizeSetupBlocks original40 = normalizeSetupBlocks target40 := by
  exact congrArg normalizeSetupBlocks (show original40 = target40 from rfl)

theorem chunkLength40 : (original40.map Setup.Block.length).sum = 1320 := by decide +kernel

column_blocks_part original41 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 5248 stop 5376
column_blocks_part target41Region6 from Verification.byteShiftColumn4 start 5248 stop 5376
noncomputable def target41 : List Setup.Block := target41Region6

theorem chunkChecked41 : normalizeSetupBlocks original41 = normalizeSetupBlocks target41 := by
  exact congrArg normalizeSetupBlocks (show original41 = target41 from rfl)

theorem chunkLength41 : (original41.map Setup.Block.length).sum = 1472 := by decide +kernel

column_blocks_part original42 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 5376 stop 5504
column_blocks_part target42Region6 from Verification.byteShiftColumn4 start 5376 stop 5504
noncomputable def target42 : List Setup.Block := target42Region6

theorem chunkChecked42 : normalizeSetupBlocks original42 = normalizeSetupBlocks target42 := by
  exact congrArg normalizeSetupBlocks (show original42 = target42 from rfl)

theorem chunkLength42 : (original42.map Setup.Block.length).sum = 1112 := by decide +kernel

column_blocks_part original43 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 5504 stop 5632
column_blocks_part target43Region6 from Verification.byteShiftColumn4 start 5504 stop 5632
noncomputable def target43 : List Setup.Block := target43Region6

theorem chunkChecked43 : normalizeSetupBlocks original43 = normalizeSetupBlocks target43 := by
  exact congrArg normalizeSetupBlocks (show original43 = target43 from rfl)

theorem chunkLength43 : (original43.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original44 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 5632 stop 5760
column_blocks_part target44Region6 from Verification.byteShiftColumn4 start 5632 stop 5760
noncomputable def target44 : List Setup.Block := target44Region6

theorem chunkChecked44 : normalizeSetupBlocks original44 = normalizeSetupBlocks target44 := by
  exact congrArg normalizeSetupBlocks (show original44 = target44 from rfl)

theorem chunkLength44 : (original44.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part original45 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 5760 stop 5888
column_blocks_part target45Region6 from Verification.byteShiftColumn4 start 5760 stop 5888
noncomputable def target45 : List Setup.Block := target45Region6

theorem chunkChecked45 : normalizeSetupBlocks original45 = normalizeSetupBlocks target45 := by
  exact congrArg normalizeSetupBlocks (show original45 = target45 from rfl)

theorem chunkLength45 : (original45.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original46 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 5888 stop 6016
column_blocks_part target46Region6 from Verification.byteShiftColumn4 start 5888 stop 6016
noncomputable def target46 : List Setup.Block := target46Region6

theorem chunkChecked46 : normalizeSetupBlocks original46 = normalizeSetupBlocks target46 := by
  exact congrArg normalizeSetupBlocks (show original46 = target46 from rfl)

theorem chunkLength46 : (original46.map Setup.Block.length).sum = 1272 := by decide +kernel

column_blocks_part original47 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 6016 stop 6144
column_blocks_part target47Region6 from Verification.byteShiftColumn4 start 6016 stop 6144
noncomputable def target47 : List Setup.Block := target47Region6

theorem chunkChecked47 : normalizeSetupBlocks original47 = normalizeSetupBlocks target47 := by
  exact congrArg normalizeSetupBlocks (show original47 = target47 from rfl)

theorem chunkLength47 : (original47.map Setup.Block.length).sum = 1256 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column4
