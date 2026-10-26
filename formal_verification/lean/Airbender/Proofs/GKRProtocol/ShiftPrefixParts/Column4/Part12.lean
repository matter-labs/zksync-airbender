import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original96 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 12288 stop 12416
column_blocks_part target96Region6 from Verification.byteShiftColumn4 start 12288 stop 12416
noncomputable def target96 : List Setup.Block := target96Region6

theorem chunkChecked96 : normalizeSetupBlocks original96 = normalizeSetupBlocks target96 := by
  exact congrArg normalizeSetupBlocks (show original96 = target96 from rfl)

theorem chunkLength96 : (original96.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part original97 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 12416 stop 12544
column_blocks_part target97Region6 from Verification.byteShiftColumn4 start 12416 stop 12544
noncomputable def target97 : List Setup.Block := target97Region6

theorem chunkChecked97 : normalizeSetupBlocks original97 = normalizeSetupBlocks target97 := by
  exact congrArg normalizeSetupBlocks (show original97 = target97 from rfl)

theorem chunkLength97 : (original97.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original98 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 12544 stop 12672
column_blocks_part target98Region6 from Verification.byteShiftColumn4 start 12544 stop 12672
noncomputable def target98 : List Setup.Block := target98Region6

theorem chunkChecked98 : normalizeSetupBlocks original98 = normalizeSetupBlocks target98 := by
  exact congrArg normalizeSetupBlocks (show original98 = target98 from rfl)

theorem chunkLength98 : (original98.map Setup.Block.length).sum = 1272 := by decide +kernel

column_blocks_part original99 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 12672 stop 12800
column_blocks_part target99Region6 from Verification.byteShiftColumn4 start 12672 stop 12800
noncomputable def target99 : List Setup.Block := target99Region6

theorem chunkChecked99 : normalizeSetupBlocks original99 = normalizeSetupBlocks target99 := by
  exact congrArg normalizeSetupBlocks (show original99 = target99 from rfl)

theorem chunkLength99 : (original99.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original100 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 12800 stop 12928
column_blocks_part target100Region6 from Verification.byteShiftColumn4 start 12800 stop 12928
noncomputable def target100 : List Setup.Block := target100Region6

theorem chunkChecked100 : normalizeSetupBlocks original100 = normalizeSetupBlocks target100 := by
  exact congrArg normalizeSetupBlocks (show original100 = target100 from rfl)

theorem chunkLength100 : (original100.map Setup.Block.length).sum = 1296 := by decide +kernel

column_blocks_part original101 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 12928 stop 13056
column_blocks_part target101Region6 from Verification.byteShiftColumn4 start 12928 stop 13056
noncomputable def target101 : List Setup.Block := target101Region6

theorem chunkChecked101 : normalizeSetupBlocks original101 = normalizeSetupBlocks target101 := by
  exact congrArg normalizeSetupBlocks (show original101 = target101 from rfl)

theorem chunkLength101 : (original101.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original102 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 13056 stop 13184
column_blocks_part target102Region6 from Verification.byteShiftColumn4 start 13056 stop 13184
noncomputable def target102 : List Setup.Block := target102Region6

theorem chunkChecked102 : normalizeSetupBlocks original102 = normalizeSetupBlocks target102 := by
  exact congrArg normalizeSetupBlocks (show original102 = target102 from rfl)

theorem chunkLength102 : (original102.map Setup.Block.length).sum = 1112 := by decide +kernel

column_blocks_part original103 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 13184 stop 13312
column_blocks_part target103Region6 from Verification.byteShiftColumn4 start 13184 stop 13312
noncomputable def target103 : List Setup.Block := target103Region6

theorem chunkChecked103 : normalizeSetupBlocks original103 = normalizeSetupBlocks target103 := by
  exact congrArg normalizeSetupBlocks (show original103 = target103 from rfl)

theorem chunkLength103 : (original103.map Setup.Block.length).sum = 1280 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column4
