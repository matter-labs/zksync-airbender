import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original16 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2048 stop 2176
column_blocks_part target16Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 251 stop 379
noncomputable def target16 : List Setup.Block := target16Region4

theorem chunkChecked16 : normalizeSetupBlocks original16 = normalizeSetupBlocks target16 := by
  exact congrArg normalizeSetupBlocks (show original16 = target16 from rfl)

theorem chunkLength16 : (original16.map Setup.Block.length).sum = 2644 := by decide +kernel

column_blocks_part original17 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2176 stop 2304
column_blocks_part target17Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 379 stop 507
noncomputable def target17 : List Setup.Block := target17Region4

theorem chunkChecked17 : normalizeSetupBlocks original17 = normalizeSetupBlocks target17 := by
  exact congrArg normalizeSetupBlocks (show original17 = target17 from rfl)

theorem chunkLength17 : (original17.map Setup.Block.length).sum = 15808 := by decide +kernel

column_blocks_part original18 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2304 stop 2432
column_blocks_part target18Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 507 stop 635
noncomputable def target18 : List Setup.Block := target18Region4

theorem chunkChecked18 : normalizeSetupBlocks original18 = normalizeSetupBlocks target18 := by
  exact congrArg normalizeSetupBlocks (show original18 = target18 from rfl)

theorem chunkLength18 : (original18.map Setup.Block.length).sum = 3280 := by decide +kernel

column_blocks_part original19 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2432 stop 2560
column_blocks_part target19Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 635 stop 763
noncomputable def target19 : List Setup.Block := target19Region4

theorem chunkChecked19 : normalizeSetupBlocks original19 = normalizeSetupBlocks target19 := by
  exact congrArg normalizeSetupBlocks (show original19 = target19 from rfl)

theorem chunkLength19 : (original19.map Setup.Block.length).sum = 1472 := by decide +kernel

column_blocks_part original20 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2560 stop 2688
column_blocks_part target20Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 763 stop 891
noncomputable def target20 : List Setup.Block := target20Region4

theorem chunkChecked20 : normalizeSetupBlocks original20 = normalizeSetupBlocks target20 := by
  exact congrArg normalizeSetupBlocks (show original20 = target20 from rfl)

theorem chunkLength20 : (original20.map Setup.Block.length).sum = 18800 := by decide +kernel

column_blocks_part original21 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2688 stop 2704
column_blocks_part target21Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 891 stop 898
column_blocks_part target21Region5 from (Verification.byteTruncateData.columns[(2 : Nat)]) start 0 stop 8
column_blocks_part target21Region6 from Verification.byteShiftColumn2 start 0 stop 1
noncomputable def target21 : List Setup.Block := target21Region4 ++ target21Region5 ++ target21Region6

theorem chunkChecked21 : normalizeSetupBlocks original21 = normalizeSetupBlocks target21 := by
  exact congrArg normalizeSetupBlocks (show original21 = target21 from rfl)

theorem chunkLength21 : (original21.map Setup.Block.length).sum = 329472 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column2
