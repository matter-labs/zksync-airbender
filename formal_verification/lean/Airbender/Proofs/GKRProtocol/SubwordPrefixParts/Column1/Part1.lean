import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.SubwordMemory
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Compiler.SubwordPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original8 from Data.GKRSetup.SubwordMemory.setupColumn1 start 8 stop 9
column_blocks_part target8Region4 from (Verification.loadByteData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def target8 : List Setup.Block := target8Region4

column_blocks_part original9 from Data.GKRSetup.SubwordMemory.setupColumn1 start 9 stop 10
column_blocks_part target9Region4 from (Verification.loadByteData.columns[(1 : Nat)]) start 2 stop 3
noncomputable def target9 : List Setup.Block := target9Region4

column_blocks_part original10 from Data.GKRSetup.SubwordMemory.setupColumn1 start 10 stop 11
column_blocks_part target10Region4 from (Verification.loadByteData.columns[(1 : Nat)]) start 3 stop 4
noncomputable def target10 : List Setup.Block := target10Region4

column_blocks_part original11 from Data.GKRSetup.SubwordMemory.setupColumn1 start 11 stop 12
column_blocks_part target11Region4 from (Verification.loadByteData.columns[(1 : Nat)]) start 4 stop 5
noncomputable def target11 : List Setup.Block := target11Region4

column_blocks_part original12 from Data.GKRSetup.SubwordMemory.setupColumn1 start 12 stop 13
column_blocks_part target12Region5 from (Verification.subwordROMHalfData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def target12 : List Setup.Block := target12Region5

theorem chunkChecked12 : normalizeSetupBlocks original12 = normalizeSetupBlocks target12 := by
  exact congrArg normalizeSetupBlocks (show original12 = target12 from rfl)

theorem chunkLength12 : (original12.map Setup.Block.length).sum = 16 := by decide +kernel

column_blocks_part original13 from Data.GKRSetup.SubwordMemory.setupColumn1 start 13 stop 14
column_blocks_part target13Region5 from (Verification.subwordROMHalfData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def target13 : List Setup.Block := target13Region5

theorem chunkChecked13 : normalizeSetupBlocks original13 = normalizeSetupBlocks target13 := by
  exact congrArg normalizeSetupBlocks (show original13 = target13 from rfl)

theorem chunkLength13 : (original13.map Setup.Block.length).sum = 4194288 := by decide +kernel

column_blocks_part original14 from Data.GKRSetup.SubwordMemory.setupColumn1 start 14 stop 15
column_blocks_part target14Region6 from (Verification.subwordROMByteData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def target14 : List Setup.Block := target14Region6

theorem chunkChecked14 : normalizeSetupBlocks original14 = normalizeSetupBlocks target14 := by
  exact congrArg normalizeSetupBlocks (show original14 = target14 from rfl)

theorem chunkLength14 : (original14.map Setup.Block.length).sum = 31 := by decide +kernel

column_blocks_part original15 from Data.GKRSetup.SubwordMemory.setupColumn1 start 15 stop 16
column_blocks_part target15Region6 from (Verification.subwordROMByteData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def target15 : List Setup.Block := target15Region6

theorem chunkChecked15 : normalizeSetupBlocks original15 = normalizeSetupBlocks target15 := by
  exact congrArg normalizeSetupBlocks (show original15 = target15 from rfl)

theorem chunkLength15 : (original15.map Setup.Block.length).sum = 8388577 := by decide +kernel

end Airbender.Compiler.SubwordPrefixNative.Column1
