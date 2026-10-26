import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original16 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 2048 stop 2176
column_blocks_part target16Region6 from Verification.byteShiftColumn4 start 2048 stop 2176
noncomputable def target16 : List Setup.Block := target16Region6

theorem chunkChecked16 : normalizeSetupBlocks original16 = normalizeSetupBlocks target16 := by
  exact congrArg normalizeSetupBlocks (show original16 = target16 from rfl)

theorem chunkLength16 : (original16.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original17 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 2176 stop 2304
column_blocks_part target17Region6 from Verification.byteShiftColumn4 start 2176 stop 2304
noncomputable def target17 : List Setup.Block := target17Region6

theorem chunkChecked17 : normalizeSetupBlocks original17 = normalizeSetupBlocks target17 := by
  exact congrArg normalizeSetupBlocks (show original17 = target17 from rfl)

theorem chunkLength17 : (original17.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original18 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 2304 stop 2432
column_blocks_part target18Region6 from Verification.byteShiftColumn4 start 2304 stop 2432
noncomputable def target18 : List Setup.Block := target18Region6

theorem chunkChecked18 : normalizeSetupBlocks original18 = normalizeSetupBlocks target18 := by
  exact congrArg normalizeSetupBlocks (show original18 = target18 from rfl)

theorem chunkLength18 : (original18.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original19 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 2432 stop 2560
column_blocks_part target19Region6 from Verification.byteShiftColumn4 start 2432 stop 2560
noncomputable def target19 : List Setup.Block := target19Region6

theorem chunkChecked19 : normalizeSetupBlocks original19 = normalizeSetupBlocks target19 := by
  exact congrArg normalizeSetupBlocks (show original19 = target19 from rfl)

theorem chunkLength19 : (original19.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original20 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 2560 stop 2688
column_blocks_part target20Region6 from Verification.byteShiftColumn4 start 2560 stop 2688
noncomputable def target20 : List Setup.Block := target20Region6

theorem chunkChecked20 : normalizeSetupBlocks original20 = normalizeSetupBlocks target20 := by
  exact congrArg normalizeSetupBlocks (show original20 = target20 from rfl)

theorem chunkLength20 : (original20.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original21 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 2688 stop 2816
column_blocks_part target21Region6 from Verification.byteShiftColumn4 start 2688 stop 2816
noncomputable def target21 : List Setup.Block := target21Region6

theorem chunkChecked21 : normalizeSetupBlocks original21 = normalizeSetupBlocks target21 := by
  exact congrArg normalizeSetupBlocks (show original21 = target21 from rfl)

theorem chunkLength21 : (original21.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original22 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 2816 stop 2944
column_blocks_part target22Region6 from Verification.byteShiftColumn4 start 2816 stop 2944
noncomputable def target22 : List Setup.Block := target22Region6

theorem chunkChecked22 : normalizeSetupBlocks original22 = normalizeSetupBlocks target22 := by
  exact congrArg normalizeSetupBlocks (show original22 = target22 from rfl)

theorem chunkLength22 : (original22.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original23 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 2944 stop 3072
column_blocks_part target23Region6 from Verification.byteShiftColumn4 start 2944 stop 3072
noncomputable def target23 : List Setup.Block := target23Region6

theorem chunkChecked23 : normalizeSetupBlocks original23 = normalizeSetupBlocks target23 := by
  exact congrArg normalizeSetupBlocks (show original23 = target23 from rfl)

theorem chunkLength23 : (original23.map Setup.Block.length).sum = 2048 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column4
