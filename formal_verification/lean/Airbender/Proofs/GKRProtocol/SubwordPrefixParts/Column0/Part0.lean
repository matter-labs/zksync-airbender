import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.SubwordMemory
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Compiler.SubwordPrefixNative.Column0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original0 from Data.GKRSetup.SubwordMemory.setupColumn0 start 0 stop 1
column_blocks_part target0Region0 from (Verification.subwordZeroData.columns[(0 : Nat)]) start 0 stop 1
noncomputable def target0 : List Setup.Block := target0Region0

column_blocks_part original1 from Data.GKRSetup.SubwordMemory.setupColumn0 start 1 stop 2
column_blocks_part target1Region1 from (Verification.storePlaceData.columns[(0 : Nat)]) start 0 stop 1
noncomputable def target1 : List Setup.Block := target1Region1

column_blocks_part original2 from Data.GKRSetup.SubwordMemory.setupColumn0 start 2 stop 3
column_blocks_part target2Region2 from (Verification.storeClearData.columns[(0 : Nat)]) start 0 stop 1
noncomputable def target2 : List Setup.Block := target2Region2

column_blocks_part original3 from Data.GKRSetup.SubwordMemory.setupColumn0 start 3 stop 4
column_blocks_part target3Region3 from (Verification.loadHalfData.columns[(0 : Nat)]) start 0 stop 1
noncomputable def target3 : List Setup.Block := target3Region3

column_blocks_part original4 from Data.GKRSetup.SubwordMemory.setupColumn0 start 4 stop 5
column_blocks_part target4Region4 from (Verification.loadByteData.columns[(0 : Nat)]) start 0 stop 1
noncomputable def target4 : List Setup.Block := target4Region4

column_blocks_part original5 from Data.GKRSetup.SubwordMemory.setupColumn0 start 5 stop 6
column_blocks_part target5Region5 from (Verification.subwordROMHalfData.columns[(0 : Nat)]) start 0 stop 1
noncomputable def target5 : List Setup.Block := target5Region5

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  exact congrArg normalizeSetupBlocks (show original5 = target5 from rfl)

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 4194304 := by decide +kernel

column_blocks_part original6 from Data.GKRSetup.SubwordMemory.setupColumn0 start 6 stop 7
column_blocks_part target6Region6 from (Verification.subwordROMByteData.columns[(0 : Nat)]) start 0 stop 1
noncomputable def target6 : List Setup.Block := target6Region6

theorem chunkChecked6 : normalizeSetupBlocks original6 = normalizeSetupBlocks target6 := by
  exact congrArg normalizeSetupBlocks (show original6 = target6 from rfl)

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 8388608 := by decide +kernel

end Airbender.Compiler.SubwordPrefixNative.Column0
