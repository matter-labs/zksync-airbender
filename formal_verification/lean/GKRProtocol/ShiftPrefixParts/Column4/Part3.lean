import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original24 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 3072 stop 3200
column_blocks_part target24Region6 from Verification.byteShiftColumn4 start 3072 stop 3200
noncomputable def target24 : List Setup.Block := target24Region6

theorem chunkChecked24 : normalizeSetupBlocks original24 = normalizeSetupBlocks target24 := by
  exact congrArg normalizeSetupBlocks (show original24 = target24 from rfl)

theorem chunkLength24 : (original24.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original25 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 3200 stop 3328
column_blocks_part target25Region6 from Verification.byteShiftColumn4 start 3200 stop 3328
noncomputable def target25 : List Setup.Block := target25Region6

theorem chunkChecked25 : normalizeSetupBlocks original25 = normalizeSetupBlocks target25 := by
  exact congrArg normalizeSetupBlocks (show original25 = target25 from rfl)

theorem chunkLength25 : (original25.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original26 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 3328 stop 3456
column_blocks_part target26Region6 from Verification.byteShiftColumn4 start 3328 stop 3456
noncomputable def target26 : List Setup.Block := target26Region6

theorem chunkChecked26 : normalizeSetupBlocks original26 = normalizeSetupBlocks target26 := by
  exact congrArg normalizeSetupBlocks (show original26 = target26 from rfl)

theorem chunkLength26 : (original26.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original27 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 3456 stop 3584
column_blocks_part target27Region6 from Verification.byteShiftColumn4 start 3456 stop 3584
noncomputable def target27 : List Setup.Block := target27Region6

theorem chunkChecked27 : normalizeSetupBlocks original27 = normalizeSetupBlocks target27 := by
  exact congrArg normalizeSetupBlocks (show original27 = target27 from rfl)

theorem chunkLength27 : (original27.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original28 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 3584 stop 3712
column_blocks_part target28Region6 from Verification.byteShiftColumn4 start 3584 stop 3712
noncomputable def target28 : List Setup.Block := target28Region6

theorem chunkChecked28 : normalizeSetupBlocks original28 = normalizeSetupBlocks target28 := by
  exact congrArg normalizeSetupBlocks (show original28 = target28 from rfl)

theorem chunkLength28 : (original28.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original29 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 3712 stop 3840
column_blocks_part target29Region6 from Verification.byteShiftColumn4 start 3712 stop 3840
noncomputable def target29 : List Setup.Block := target29Region6

theorem chunkChecked29 : normalizeSetupBlocks original29 = normalizeSetupBlocks target29 := by
  exact congrArg normalizeSetupBlocks (show original29 = target29 from rfl)

theorem chunkLength29 : (original29.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original30 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 3840 stop 3968
column_blocks_part target30Region6 from Verification.byteShiftColumn4 start 3840 stop 3968
noncomputable def target30 : List Setup.Block := target30Region6

theorem chunkChecked30 : normalizeSetupBlocks original30 = normalizeSetupBlocks target30 := by
  exact congrArg normalizeSetupBlocks (show original30 = target30 from rfl)

theorem chunkLength30 : (original30.map Setup.Block.length).sum = 2120 := by decide +kernel

column_blocks_part original31 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 3968 stop 4096
column_blocks_part target31Region6 from Verification.byteShiftColumn4 start 3968 stop 4096
noncomputable def target31 : List Setup.Block := target31Region6

theorem chunkChecked31 : normalizeSetupBlocks original31 = normalizeSetupBlocks target31 := by
  exact congrArg normalizeSetupBlocks (show original31 = target31 from rfl)

theorem chunkLength31 : (original31.map Setup.Block.length).sum = 1792 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column4
