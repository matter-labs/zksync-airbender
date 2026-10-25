import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original48 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 6144 stop 6272
column_blocks_part target48Region6 from Verification.byteShiftColumn7 start 6144 stop 6272
noncomputable def target48 : List Setup.Block := target48Region6

theorem chunkChecked48 : normalizeSetupBlocks original48 = normalizeSetupBlocks target48 := by
  exact congrArg normalizeSetupBlocks (show original48 = target48 from rfl)

theorem chunkLength48 : (original48.map Setup.Block.length).sum = 1200 := by decide +kernel

column_blocks_part original49 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 6272 stop 6400
column_blocks_part target49Region6 from Verification.byteShiftColumn7 start 6272 stop 6400
noncomputable def target49 : List Setup.Block := target49Region6

theorem chunkChecked49 : normalizeSetupBlocks original49 = normalizeSetupBlocks target49 := by
  exact congrArg normalizeSetupBlocks (show original49 = target49 from rfl)

theorem chunkLength49 : (original49.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original50 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 6400 stop 6528
column_blocks_part target50Region6 from Verification.byteShiftColumn7 start 6400 stop 6528
noncomputable def target50 : List Setup.Block := target50Region6

theorem chunkChecked50 : normalizeSetupBlocks original50 = normalizeSetupBlocks target50 := by
  exact congrArg normalizeSetupBlocks (show original50 = target50 from rfl)

theorem chunkLength50 : (original50.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part original51 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 6528 stop 6656
column_blocks_part target51Region6 from Verification.byteShiftColumn7 start 6528 stop 6656
noncomputable def target51 : List Setup.Block := target51Region6

theorem chunkChecked51 : normalizeSetupBlocks original51 = normalizeSetupBlocks target51 := by
  exact congrArg normalizeSetupBlocks (show original51 = target51 from rfl)

theorem chunkLength51 : (original51.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original52 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 6656 stop 6784
column_blocks_part target52Region6 from Verification.byteShiftColumn7 start 6656 stop 6784
noncomputable def target52 : List Setup.Block := target52Region6

theorem chunkChecked52 : normalizeSetupBlocks original52 = normalizeSetupBlocks target52 := by
  exact congrArg normalizeSetupBlocks (show original52 = target52 from rfl)

theorem chunkLength52 : (original52.map Setup.Block.length).sum = 1200 := by decide +kernel

column_blocks_part original53 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 6784 stop 6912
column_blocks_part target53Region6 from Verification.byteShiftColumn7 start 6784 stop 6912
noncomputable def target53 : List Setup.Block := target53Region6

theorem chunkChecked53 : normalizeSetupBlocks original53 = normalizeSetupBlocks target53 := by
  exact congrArg normalizeSetupBlocks (show original53 = target53 from rfl)

theorem chunkLength53 : (original53.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original54 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 6912 stop 7040
column_blocks_part target54Region6 from Verification.byteShiftColumn7 start 6912 stop 7040
noncomputable def target54 : List Setup.Block := target54Region6

theorem chunkChecked54 : normalizeSetupBlocks original54 = normalizeSetupBlocks target54 := by
  exact congrArg normalizeSetupBlocks (show original54 = target54 from rfl)

theorem chunkLength54 : (original54.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part original55 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 7040 stop 7168
column_blocks_part target55Region6 from Verification.byteShiftColumn7 start 7040 stop 7168
noncomputable def target55 : List Setup.Block := target55Region6

theorem chunkChecked55 : normalizeSetupBlocks original55 = normalizeSetupBlocks target55 := by
  exact congrArg normalizeSetupBlocks (show original55 = target55 from rfl)

theorem chunkLength55 : (original55.map Setup.Block.length).sum = 1048 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column7
