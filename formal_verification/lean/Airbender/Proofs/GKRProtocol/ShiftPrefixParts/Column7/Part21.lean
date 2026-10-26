import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original168 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 21504 stop 21632
column_blocks_part target168Region6 from Verification.byteShiftColumn7 start 21504 stop 21632
noncomputable def target168 : List Setup.Block := target168Region6

theorem chunkChecked168 : normalizeSetupBlocks original168 = normalizeSetupBlocks target168 := by
  exact congrArg normalizeSetupBlocks (show original168 = target168 from rfl)

theorem chunkLength168 : (original168.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part original169 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 21632 stop 21760
column_blocks_part target169Region6 from Verification.byteShiftColumn7 start 21632 stop 21760
noncomputable def target169 : List Setup.Block := target169Region6

theorem chunkChecked169 : normalizeSetupBlocks original169 = normalizeSetupBlocks target169 := by
  exact congrArg normalizeSetupBlocks (show original169 = target169 from rfl)

theorem chunkLength169 : (original169.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original170 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 21760 stop 21888
column_blocks_part target170Region6 from Verification.byteShiftColumn7 start 21760 stop 21888
noncomputable def target170 : List Setup.Block := target170Region6

theorem chunkChecked170 : normalizeSetupBlocks original170 = normalizeSetupBlocks target170 := by
  exact congrArg normalizeSetupBlocks (show original170 = target170 from rfl)

theorem chunkLength170 : (original170.map Setup.Block.length).sum = 2272 := by decide +kernel

column_blocks_part original171 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 21888 stop 22016
column_blocks_part target171Region6 from Verification.byteShiftColumn7 start 21888 stop 22016
noncomputable def target171 : List Setup.Block := target171Region6

theorem chunkChecked171 : normalizeSetupBlocks original171 = normalizeSetupBlocks target171 := by
  exact congrArg normalizeSetupBlocks (show original171 = target171 from rfl)

theorem chunkLength171 : (original171.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original172 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 22016 stop 22144
column_blocks_part target172Region6 from Verification.byteShiftColumn7 start 22016 stop 22144
noncomputable def target172 : List Setup.Block := target172Region6

theorem chunkChecked172 : normalizeSetupBlocks original172 = normalizeSetupBlocks target172 := by
  exact congrArg normalizeSetupBlocks (show original172 = target172 from rfl)

theorem chunkLength172 : (original172.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part original173 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 22144 stop 22272
column_blocks_part target173Region6 from Verification.byteShiftColumn7 start 22144 stop 22272
noncomputable def target173 : List Setup.Block := target173Region6

theorem chunkChecked173 : normalizeSetupBlocks original173 = normalizeSetupBlocks target173 := by
  exact congrArg normalizeSetupBlocks (show original173 = target173 from rfl)

theorem chunkLength173 : (original173.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original174 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 22272 stop 22400
column_blocks_part target174Region6 from Verification.byteShiftColumn7 start 22272 stop 22400
noncomputable def target174 : List Setup.Block := target174Region6

theorem chunkChecked174 : normalizeSetupBlocks original174 = normalizeSetupBlocks target174 := by
  exact congrArg normalizeSetupBlocks (show original174 = target174 from rfl)

theorem chunkLength174 : (original174.map Setup.Block.length).sum = 2063 := by decide +kernel

column_blocks_part original175 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 22400 stop 22528
column_blocks_part target175Region6 from Verification.byteShiftColumn7 start 22400 stop 22528
noncomputable def target175 : List Setup.Block := target175Region6

theorem chunkChecked175 : normalizeSetupBlocks original175 = normalizeSetupBlocks target175 := by
  exact congrArg normalizeSetupBlocks (show original175 = target175 from rfl)

theorem chunkLength175 : (original175.map Setup.Block.length).sum = 1985 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column7
