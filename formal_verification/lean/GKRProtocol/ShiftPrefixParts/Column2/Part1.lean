import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original8 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1024 stop 1152
column_blocks_part target8Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 125 stop 253
noncomputable def target8 : List Setup.Block := target8Region3

theorem chunkChecked8 : normalizeSetupBlocks original8 = normalizeSetupBlocks target8 := by
  exact congrArg normalizeSetupBlocks (show original8 = target8 from rfl)

theorem chunkLength8 : (original8.map Setup.Block.length).sum = 1460 := by decide +kernel

column_blocks_part original9 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1152 stop 1280
column_blocks_part target9Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 253 stop 381
noncomputable def target9 : List Setup.Block := target9Region3

theorem chunkChecked9 : normalizeSetupBlocks original9 = normalizeSetupBlocks target9 := by
  exact congrArg normalizeSetupBlocks (show original9 = target9 from rfl)

theorem chunkLength9 : (original9.map Setup.Block.length).sum = 2700 := by decide +kernel

column_blocks_part original10 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1280 stop 1408
column_blocks_part target10Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 381 stop 509
noncomputable def target10 : List Setup.Block := target10Region3

theorem chunkChecked10 : normalizeSetupBlocks original10 = normalizeSetupBlocks target10 := by
  exact congrArg normalizeSetupBlocks (show original10 = target10 from rfl)

theorem chunkLength10 : (original10.map Setup.Block.length).sum = 16000 := by decide +kernel

column_blocks_part original11 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1408 stop 1536
column_blocks_part target11Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 509 stop 637
noncomputable def target11 : List Setup.Block := target11Region3

theorem chunkChecked11 : normalizeSetupBlocks original11 = normalizeSetupBlocks target11 := by
  exact congrArg normalizeSetupBlocks (show original11 = target11 from rfl)

theorem chunkLength11 : (original11.map Setup.Block.length).sum = 3040 := by decide +kernel

column_blocks_part original12 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1536 stop 1664
column_blocks_part target12Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 637 stop 765
noncomputable def target12 : List Setup.Block := target12Region3

theorem chunkChecked12 : normalizeSetupBlocks original12 = normalizeSetupBlocks target12 := by
  exact congrArg normalizeSetupBlocks (show original12 = target12 from rfl)

theorem chunkLength12 : (original12.map Setup.Block.length).sum = 1488 := by decide +kernel

column_blocks_part original13 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1664 stop 1792
column_blocks_part target13Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 765 stop 893
noncomputable def target13 : List Setup.Block := target13Region3

theorem chunkChecked13 : normalizeSetupBlocks original13 = normalizeSetupBlocks target13 := by
  exact congrArg normalizeSetupBlocks (show original13 = target13 from rfl)

theorem chunkLength13 : (original13.map Setup.Block.length).sum = 19280 := by decide +kernel

column_blocks_part original14 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1792 stop 1920
column_blocks_part target14Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 893 stop 898
column_blocks_part target14Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 0 stop 123
noncomputable def target14 : List Setup.Block := target14Region3 ++ target14Region4

theorem chunkChecked14 : normalizeSetupBlocks original14 = normalizeSetupBlocks target14 := by
  exact congrArg normalizeSetupBlocks (show original14 = target14 from rfl)

theorem chunkLength14 : (original14.map Setup.Block.length).sum = 21440 := by decide +kernel

column_blocks_part original15 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1920 stop 2048
column_blocks_part target15Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 123 stop 251
noncomputable def target15 : List Setup.Block := target15Region4

theorem chunkChecked15 : normalizeSetupBlocks original15 = normalizeSetupBlocks target15 := by
  exact congrArg normalizeSetupBlocks (show original15 = target15 from rfl)

theorem chunkLength15 : (original15.map Setup.Block.length).sum = 1580 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column2
