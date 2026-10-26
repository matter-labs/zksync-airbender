import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.SubwordMemory
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Compiler.SubwordPrefixNative.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original0 from Data.GKRSetup.SubwordMemory.setupColumn2 start 0 stop 1
column_blocks_part target0Region0 from (Verification.subwordZeroData.columns[(2 : Nat)]) start 0 stop 1
column_blocks_part target0Region1 from (Verification.storePlaceData.columns[(2 : Nat)]) start 0 stop 1
column_blocks_part target0Region2 from (Verification.storeClearData.columns[(2 : Nat)]) start 0 stop 1
column_blocks_part target0Region3 from (Verification.loadHalfData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def target0 : List Setup.Block := target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rfl

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 360449 := by decide +kernel

column_blocks_part original1 from Data.GKRSetup.SubwordMemory.setupColumn2 start 1 stop 2
column_blocks_part target1Region3 from (Verification.loadHalfData.columns[(2 : Nat)]) start 1 stop 2
noncomputable def target1 : List Setup.Block := target1Region3

theorem chunkChecked1 : normalizeSetupBlocks original1 = normalizeSetupBlocks target1 := by
  exact congrArg normalizeSetupBlocks (show original1 = target1 from rfl)

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 32768 := by decide +kernel

column_blocks_part original2 from Data.GKRSetup.SubwordMemory.setupColumn2 start 2 stop 3
column_blocks_part target2Region4 from (Verification.loadByteData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def target2 : List Setup.Block := target2Region4

theorem chunkChecked2 : normalizeSetupBlocks original2 = normalizeSetupBlocks target2 := by
  exact congrArg normalizeSetupBlocks (show original2 = target2 from rfl)

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 65664 := by decide +kernel

column_blocks_part original3 from Data.GKRSetup.SubwordMemory.setupColumn2 start 3 stop 4
column_blocks_part target3Region4 from (Verification.loadByteData.columns[(2 : Nat)]) start 1 stop 2
noncomputable def target3 : List Setup.Block := target3Region4

theorem chunkChecked3 : normalizeSetupBlocks original3 = normalizeSetupBlocks target3 := by
  exact congrArg normalizeSetupBlocks (show original3 = target3 from rfl)

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 65536 := by decide +kernel

column_blocks_part original4 from Data.GKRSetup.SubwordMemory.setupColumn2 start 4 stop 5
column_blocks_part target4Region4 from (Verification.loadByteData.columns[(2 : Nat)]) start 2 stop 3
noncomputable def target4 : List Setup.Block := target4Region4

theorem chunkChecked4 : normalizeSetupBlocks original4 = normalizeSetupBlocks target4 := by
  exact congrArg normalizeSetupBlocks (show original4 = target4 from rfl)

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 98176 := by decide +kernel

column_blocks_part original5 from Data.GKRSetup.SubwordMemory.setupColumn2 start 5 stop 6
column_blocks_part target5Region4 from (Verification.loadByteData.columns[(2 : Nat)]) start 3 stop 4
noncomputable def target5 : List Setup.Block := target5Region4

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  exact congrArg normalizeSetupBlocks (show original5 = target5 from rfl)

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 32768 := by decide +kernel

column_blocks_part original6 from Data.GKRSetup.SubwordMemory.setupColumn2 start 6 stop 7
column_blocks_part target6Region5 from (Verification.subwordROMHalfData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def target6 : List Setup.Block := target6Region5

theorem chunkChecked6 : normalizeSetupBlocks original6 = normalizeSetupBlocks target6 := by
  exact congrArg normalizeSetupBlocks (show original6 = target6 from rfl)

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 6 := by decide +kernel

column_blocks_part original7 from Data.GKRSetup.SubwordMemory.setupColumn2 start 7 stop 8
column_blocks_part target7Region5 from (Verification.subwordROMHalfData.columns[(2 : Nat)]) start 1 stop 2
noncomputable def target7 : List Setup.Block := target7Region5

theorem chunkChecked7 : normalizeSetupBlocks original7 = normalizeSetupBlocks target7 := by
  exact congrArg normalizeSetupBlocks (show original7 = target7 from rfl)

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 1 := by decide +kernel

end Airbender.Compiler.SubwordPrefixNative.Column2
