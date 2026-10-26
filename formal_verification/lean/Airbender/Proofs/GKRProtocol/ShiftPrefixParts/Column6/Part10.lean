import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original80 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 10240 stop 10368
column_blocks_part target80Region6 from Verification.byteShiftColumn6 start 10240 stop 10368
noncomputable def target80 : List Setup.Block := target80Region6

theorem chunkChecked80 : normalizeSetupBlocks original80 = normalizeSetupBlocks target80 := by
  exact congrArg normalizeSetupBlocks (show original80 = target80 from rfl)

theorem chunkLength80 : (original80.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original81 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 10368 stop 10496
column_blocks_part target81Region6 from Verification.byteShiftColumn6 start 10368 stop 10496
noncomputable def target81 : List Setup.Block := target81Region6

theorem chunkChecked81 : normalizeSetupBlocks original81 = normalizeSetupBlocks target81 := by
  exact congrArg normalizeSetupBlocks (show original81 = target81 from rfl)

theorem chunkLength81 : (original81.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original82 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 10496 stop 10624
column_blocks_part target82Region6 from Verification.byteShiftColumn6 start 10496 stop 10624
noncomputable def target82 : List Setup.Block := target82Region6

theorem chunkChecked82 : normalizeSetupBlocks original82 = normalizeSetupBlocks target82 := by
  exact congrArg normalizeSetupBlocks (show original82 = target82 from rfl)

theorem chunkLength82 : (original82.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original83 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 10624 stop 10752
column_blocks_part target83Region6 from Verification.byteShiftColumn6 start 10624 stop 10752
noncomputable def target83 : List Setup.Block := target83Region6

theorem chunkChecked83 : normalizeSetupBlocks original83 = normalizeSetupBlocks target83 := by
  exact congrArg normalizeSetupBlocks (show original83 = target83 from rfl)

theorem chunkLength83 : (original83.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original84 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 10752 stop 10880
column_blocks_part target84Region6 from Verification.byteShiftColumn6 start 10752 stop 10880
noncomputable def target84 : List Setup.Block := target84Region6

theorem chunkChecked84 : normalizeSetupBlocks original84 = normalizeSetupBlocks target84 := by
  exact congrArg normalizeSetupBlocks (show original84 = target84 from rfl)

theorem chunkLength84 : (original84.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original85 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 10880 stop 11008
column_blocks_part target85Region6 from Verification.byteShiftColumn6 start 10880 stop 11008
noncomputable def target85 : List Setup.Block := target85Region6

theorem chunkChecked85 : normalizeSetupBlocks original85 = normalizeSetupBlocks target85 := by
  exact congrArg normalizeSetupBlocks (show original85 = target85 from rfl)

theorem chunkLength85 : (original85.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original86 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 11008 stop 11136
column_blocks_part target86Region6 from Verification.byteShiftColumn6 start 11008 stop 11136
noncomputable def target86 : List Setup.Block := target86Region6

theorem chunkChecked86 : normalizeSetupBlocks original86 = normalizeSetupBlocks target86 := by
  exact congrArg normalizeSetupBlocks (show original86 = target86 from rfl)

theorem chunkLength86 : (original86.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original87 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 11136 stop 11264
column_blocks_part target87Region6 from Verification.byteShiftColumn6 start 11136 stop 11264
noncomputable def target87 : List Setup.Block := target87Region6

theorem chunkChecked87 : normalizeSetupBlocks original87 = normalizeSetupBlocks target87 := by
  exact congrArg normalizeSetupBlocks (show original87 = target87 from rfl)

theorem chunkLength87 : (original87.map Setup.Block.length).sum = 1080 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
