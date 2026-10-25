import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original120 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 15360 stop 15488
column_blocks_part target120Region6 from Verification.byteShiftColumn5 start 15360 stop 15488
noncomputable def target120 : List Setup.Block := target120Region6

theorem chunkChecked120 : normalizeSetupBlocks original120 = normalizeSetupBlocks target120 := by
  exact congrArg normalizeSetupBlocks (show original120 = target120 from rfl)

theorem chunkLength120 : (original120.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original121 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 15488 stop 15616
column_blocks_part target121Region6 from Verification.byteShiftColumn5 start 15488 stop 15616
noncomputable def target121 : List Setup.Block := target121Region6

theorem chunkChecked121 : normalizeSetupBlocks original121 = normalizeSetupBlocks target121 := by
  exact congrArg normalizeSetupBlocks (show original121 = target121 from rfl)

theorem chunkLength121 : (original121.map Setup.Block.length).sum = 1186 := by decide +kernel

column_blocks_part original122 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 15616 stop 15744
column_blocks_part target122Region6 from Verification.byteShiftColumn5 start 15616 stop 15744
noncomputable def target122 : List Setup.Block := target122Region6

theorem chunkChecked122 : normalizeSetupBlocks original122 = normalizeSetupBlocks target122 := by
  exact congrArg normalizeSetupBlocks (show original122 = target122 from rfl)

theorem chunkLength122 : (original122.map Setup.Block.length).sum = 1046 := by decide +kernel

column_blocks_part original123 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 15744 stop 15872
column_blocks_part target123Region6 from Verification.byteShiftColumn5 start 15744 stop 15872
noncomputable def target123 : List Setup.Block := target123Region6

theorem chunkChecked123 : normalizeSetupBlocks original123 = normalizeSetupBlocks target123 := by
  exact congrArg normalizeSetupBlocks (show original123 = target123 from rfl)

theorem chunkLength123 : (original123.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original124 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 15872 stop 16000
column_blocks_part target124Region6 from Verification.byteShiftColumn5 start 15872 stop 16000
noncomputable def target124 : List Setup.Block := target124Region6

theorem chunkChecked124 : normalizeSetupBlocks original124 = normalizeSetupBlocks target124 := by
  exact congrArg normalizeSetupBlocks (show original124 = target124 from rfl)

theorem chunkLength124 : (original124.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original125 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 16000 stop 16128
column_blocks_part target125Region6 from Verification.byteShiftColumn5 start 16000 stop 16128
noncomputable def target125 : List Setup.Block := target125Region6

theorem chunkChecked125 : normalizeSetupBlocks original125 = normalizeSetupBlocks target125 := by
  exact congrArg normalizeSetupBlocks (show original125 = target125 from rfl)

theorem chunkLength125 : (original125.map Setup.Block.length).sum = 1192 := by decide +kernel

column_blocks_part original126 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 16128 stop 16256
column_blocks_part target126Region6 from Verification.byteShiftColumn5 start 16128 stop 16256
noncomputable def target126 : List Setup.Block := target126Region6

theorem chunkChecked126 : normalizeSetupBlocks original126 = normalizeSetupBlocks target126 := by
  exact congrArg normalizeSetupBlocks (show original126 = target126 from rfl)

theorem chunkLength126 : (original126.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original127 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 16256 stop 16384
column_blocks_part target127Region6 from Verification.byteShiftColumn5 start 16256 stop 16384
noncomputable def target127 : List Setup.Block := target127Region6

theorem chunkChecked127 : normalizeSetupBlocks original127 = normalizeSetupBlocks target127 := by
  exact congrArg normalizeSetupBlocks (show original127 = target127 from rfl)

theorem chunkLength127 : (original127.map Setup.Block.length).sum = 1064 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column5
