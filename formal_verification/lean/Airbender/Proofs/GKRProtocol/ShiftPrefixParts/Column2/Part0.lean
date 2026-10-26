import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original0 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 0 stop 128
column_blocks_part target0Region0 from (Verification.byteZeroData.columns[(2 : Nat)]) start 0 stop 1
column_blocks_part target0Region1 from (Verification.byteSignData.columns[(2 : Nat)]) start 0 stop 1
column_blocks_part target0Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 0 stop 128
noncomputable def target0 : List Setup.Block := target0Region0 ++ target0Region1 ++ target0Region2

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rfl

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 20673 := by decide +kernel

column_blocks_part original1 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 128 stop 256
column_blocks_part target1Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 128 stop 256
noncomputable def target1 : List Setup.Block := target1Region2

theorem chunkChecked1 : normalizeSetupBlocks original1 = normalizeSetupBlocks target1 := by
  exact congrArg normalizeSetupBlocks (show original1 = target1 from rfl)

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 1340 := by decide +kernel

column_blocks_part original2 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 256 stop 384
column_blocks_part target2Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 256 stop 384
noncomputable def target2 : List Setup.Block := target2Region2

theorem chunkChecked2 : normalizeSetupBlocks original2 = normalizeSetupBlocks target2 := by
  exact congrArg normalizeSetupBlocks (show original2 = target2 from rfl)

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 2756 := by decide +kernel

column_blocks_part original3 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 384 stop 512
column_blocks_part target3Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 384 stop 512
noncomputable def target3 : List Setup.Block := target3Region2

theorem chunkChecked3 : normalizeSetupBlocks original3 = normalizeSetupBlocks target3 := by
  exact congrArg normalizeSetupBlocks (show original3 = target3 from rfl)

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 16192 := by decide +kernel

column_blocks_part original4 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 512 stop 640
column_blocks_part target4Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 512 stop 640
noncomputable def target4 : List Setup.Block := target4Region2

theorem chunkChecked4 : normalizeSetupBlocks original4 = normalizeSetupBlocks target4 := by
  exact congrArg normalizeSetupBlocks (show original4 = target4 from rfl)

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 2800 := by decide +kernel

column_blocks_part original5 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 640 stop 768
column_blocks_part target5Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 640 stop 768
noncomputable def target5 : List Setup.Block := target5Region2

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  exact congrArg normalizeSetupBlocks (show original5 = target5 from rfl)

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 1504 := by decide +kernel

column_blocks_part original6 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 768 stop 896
column_blocks_part target6Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 768 stop 896
noncomputable def target6 : List Setup.Block := target6Region2

theorem chunkChecked6 : normalizeSetupBlocks original6 = normalizeSetupBlocks target6 := by
  exact congrArg normalizeSetupBlocks (show original6 = target6 from rfl)

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 19760 := by decide +kernel

column_blocks_part original7 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 896 stop 1024
column_blocks_part target7Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 896 stop 899
column_blocks_part target7Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 0 stop 125
noncomputable def target7 : List Setup.Block := target7Region2 ++ target7Region3

theorem chunkChecked7 : normalizeSetupBlocks original7 = normalizeSetupBlocks target7 := by
  exact congrArg normalizeSetupBlocks (show original7 = target7 from rfl)

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 21056 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column2
