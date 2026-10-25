import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.SubwordMemory
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Compiler.SubwordPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original0 from Data.GKRSetup.SubwordMemory.setupColumn1 start 0 stop 1
column_blocks_part target0Region0 from (Verification.subwordZeroData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def target0 : List Setup.Block := target0Region0

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  exact congrArg normalizeSetupBlocks (show original0 = target0 from rfl)

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 1 := by decide +kernel

column_blocks_part original1 from Data.GKRSetup.SubwordMemory.setupColumn1 start 1 stop 2
column_blocks_part target1Region1 from (Verification.storePlaceData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def target1 : List Setup.Block := target1Region1

theorem chunkChecked1 : normalizeSetupBlocks original1 = normalizeSetupBlocks target1 := by
  exact congrArg normalizeSetupBlocks (show original1 = target1 from rfl)

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 65536 := by decide +kernel

column_blocks_part original2 from Data.GKRSetup.SubwordMemory.setupColumn1 start 2 stop 3
column_blocks_part target2Region1 from (Verification.storePlaceData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def target2 : List Setup.Block := target2Region1

theorem chunkChecked2 : normalizeSetupBlocks original2 = normalizeSetupBlocks target2 := by
  exact congrArg normalizeSetupBlocks (show original2 = target2 from rfl)

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 65536 := by decide +kernel

column_blocks_part original3 from Data.GKRSetup.SubwordMemory.setupColumn1 start 3 stop 4
column_blocks_part target3Region2 from (Verification.storeClearData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def target3 : List Setup.Block := target3Region2

theorem chunkChecked3 : normalizeSetupBlocks original3 = normalizeSetupBlocks target3 := by
  exact congrArg normalizeSetupBlocks (show original3 = target3 from rfl)

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 65536 := by decide +kernel

column_blocks_part original4 from Data.GKRSetup.SubwordMemory.setupColumn1 start 4 stop 5
column_blocks_part target4Region2 from (Verification.storeClearData.columns[(1 : Nat)]) start 1 stop 2
column_blocks_part target4Region3 from (Verification.loadHalfData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def target4 : List Setup.Block := target4Region2 ++ target4Region3

theorem chunkChecked4 : normalizeSetupBlocks original4 = normalizeSetupBlocks target4 := by
  rfl

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 65792 := by decide +kernel

column_blocks_part original5 from Data.GKRSetup.SubwordMemory.setupColumn1 start 5 stop 6
column_blocks_part target5Region3 from (Verification.loadHalfData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def target5 : List Setup.Block := target5Region3

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  exact congrArg normalizeSetupBlocks (show original5 = target5 from rfl)

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 65280 := by decide +kernel

column_blocks_part original6 from Data.GKRSetup.SubwordMemory.setupColumn1 start 6 stop 7
column_blocks_part target6Region3 from (Verification.loadHalfData.columns[(1 : Nat)]) start 2 stop 3
noncomputable def target6 : List Setup.Block := target6Region3

theorem chunkChecked6 : normalizeSetupBlocks original6 = normalizeSetupBlocks target6 := by
  exact congrArg normalizeSetupBlocks (show original6 = target6 from rfl)

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 65536 := by decide +kernel

column_blocks_part original7 from Data.GKRSetup.SubwordMemory.setupColumn1 start 7 stop 8
column_blocks_part target7Region4 from (Verification.loadByteData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def target7 : List Setup.Block := target7Region4

theorem chunkChecked7 : normalizeSetupBlocks original7 = normalizeSetupBlocks target7 := by
  exact congrArg normalizeSetupBlocks (show original7 = target7 from rfl)

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 65536 := by decide +kernel

end Airbender.Compiler.SubwordPrefixNative.Column1
