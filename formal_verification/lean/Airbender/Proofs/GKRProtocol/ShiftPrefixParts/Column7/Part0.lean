import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original0 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 0 stop 128
column_blocks_part target0Region0 from (Verification.byteZeroData.columns[(7 : Nat)]) start 0 stop 1
column_blocks_part target0Region1 from (Verification.byteSignData.columns[(7 : Nat)]) start 0 stop 1
column_blocks_part target0Region2 from (Verification.byteXorData.columns[(7 : Nat)]) start 0 stop 1
column_blocks_part target0Region3 from (Verification.byteOrData.columns[(7 : Nat)]) start 0 stop 1
column_blocks_part target0Region4 from (Verification.byteAndData.columns[(7 : Nat)]) start 0 stop 1
column_blocks_part target0Region5 from (Verification.byteTruncateData.columns[(7 : Nat)]) start 0 stop 1
column_blocks_part target0Region6 from Verification.byteShiftColumn7 start 0 stop 128
noncomputable def target0 : List Setup.Block := target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3 ++ target0Region4 ++ target0Region5 ++ target0Region6

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rfl

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 264403 := by decide +kernel

column_blocks_part original1 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 128 stop 256
column_blocks_part target1Region6 from Verification.byteShiftColumn7 start 128 stop 256
noncomputable def target1 : List Setup.Block := target1Region6

theorem chunkChecked1 : normalizeSetupBlocks original1 = normalizeSetupBlocks target1 := by
  exact congrArg normalizeSetupBlocks (show original1 = target1 from rfl)

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 1520 := by decide +kernel

column_blocks_part original2 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 256 stop 384
column_blocks_part target2Region6 from Verification.byteShiftColumn7 start 256 stop 384
noncomputable def target2 : List Setup.Block := target2Region6

theorem chunkChecked2 : normalizeSetupBlocks original2 = normalizeSetupBlocks target2 := by
  exact congrArg normalizeSetupBlocks (show original2 = target2 from rfl)

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 1328 := by decide +kernel

column_blocks_part original3 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 384 stop 512
column_blocks_part target3Region6 from Verification.byteShiftColumn7 start 384 stop 512
noncomputable def target3 : List Setup.Block := target3Region6

theorem chunkChecked3 : normalizeSetupBlocks original3 = normalizeSetupBlocks target3 := by
  exact congrArg normalizeSetupBlocks (show original3 = target3 from rfl)

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 1456 := by decide +kernel

column_blocks_part original4 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 512 stop 640
column_blocks_part target4Region6 from Verification.byteShiftColumn7 start 512 stop 640
noncomputable def target4 : List Setup.Block := target4Region6

theorem chunkChecked4 : normalizeSetupBlocks original4 = normalizeSetupBlocks target4 := by
  exact congrArg normalizeSetupBlocks (show original4 = target4 from rfl)

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 1320 := by decide +kernel

column_blocks_part original5 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 640 stop 768
column_blocks_part target5Region6 from Verification.byteShiftColumn7 start 640 stop 768
noncomputable def target5 : List Setup.Block := target5Region6

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  exact congrArg normalizeSetupBlocks (show original5 = target5 from rfl)

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 1296 := by decide +kernel

column_blocks_part original6 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 768 stop 896
column_blocks_part target6Region6 from Verification.byteShiftColumn7 start 768 stop 896
noncomputable def target6 : List Setup.Block := target6Region6

theorem chunkChecked6 : normalizeSetupBlocks original6 = normalizeSetupBlocks target6 := by
  exact congrArg normalizeSetupBlocks (show original6 = target6 from rfl)

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original7 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 896 stop 1024
column_blocks_part target7Region6 from Verification.byteShiftColumn7 start 896 stop 1024
noncomputable def target7 : List Setup.Block := target7Region6

theorem chunkChecked7 : normalizeSetupBlocks original7 = normalizeSetupBlocks target7 := by
  exact congrArg normalizeSetupBlocks (show original7 = target7 from rfl)

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 1264 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column7
