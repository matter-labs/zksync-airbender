import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original56 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 7168 stop 7296
column_blocks_part target56Region6 from Verification.byteShiftColumn6 start 7168 stop 7296
noncomputable def target56 : List Setup.Block := target56Region6

theorem chunkChecked56 : normalizeSetupBlocks original56 = normalizeSetupBlocks target56 := by
  exact congrArg normalizeSetupBlocks (show original56 = target56 from rfl)

theorem chunkLength56 : (original56.map Setup.Block.length).sum = 1472 := by decide +kernel

column_blocks_part original57 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 7296 stop 7424
column_blocks_part target57Region6 from Verification.byteShiftColumn6 start 7296 stop 7424
noncomputable def target57 : List Setup.Block := target57Region6

theorem chunkChecked57 : normalizeSetupBlocks original57 = normalizeSetupBlocks target57 := by
  exact congrArg normalizeSetupBlocks (show original57 = target57 from rfl)

theorem chunkLength57 : (original57.map Setup.Block.length).sum = 1296 := by decide +kernel

column_blocks_part original58 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 7424 stop 7552
column_blocks_part target58Region6 from Verification.byteShiftColumn6 start 7424 stop 7552
noncomputable def target58 : List Setup.Block := target58Region6

theorem chunkChecked58 : normalizeSetupBlocks original58 = normalizeSetupBlocks target58 := by
  exact congrArg normalizeSetupBlocks (show original58 = target58 from rfl)

theorem chunkLength58 : (original58.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original59 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 7552 stop 7680
column_blocks_part target59Region6 from Verification.byteShiftColumn6 start 7552 stop 7680
noncomputable def target59 : List Setup.Block := target59Region6

theorem chunkChecked59 : normalizeSetupBlocks original59 = normalizeSetupBlocks target59 := by
  exact congrArg normalizeSetupBlocks (show original59 = target59 from rfl)

theorem chunkLength59 : (original59.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original60 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 7680 stop 7808
column_blocks_part target60Region6 from Verification.byteShiftColumn6 start 7680 stop 7808
noncomputable def target60 : List Setup.Block := target60Region6

theorem chunkChecked60 : normalizeSetupBlocks original60 = normalizeSetupBlocks target60 := by
  exact congrArg normalizeSetupBlocks (show original60 = target60 from rfl)

theorem chunkLength60 : (original60.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part original61 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 7808 stop 7936
column_blocks_part target61Region6 from Verification.byteShiftColumn6 start 7808 stop 7936
noncomputable def target61 : List Setup.Block := target61Region6

theorem chunkChecked61 : normalizeSetupBlocks original61 = normalizeSetupBlocks target61 := by
  exact congrArg normalizeSetupBlocks (show original61 = target61 from rfl)

theorem chunkLength61 : (original61.map Setup.Block.length).sum = 1244 := by decide +kernel

column_blocks_part original62 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 7936 stop 8064
column_blocks_part target62Region6 from Verification.byteShiftColumn6 start 7936 stop 8064
noncomputable def target62 : List Setup.Block := target62Region6

theorem chunkChecked62 : normalizeSetupBlocks original62 = normalizeSetupBlocks target62 := by
  exact congrArg normalizeSetupBlocks (show original62 = target62 from rfl)

theorem chunkLength62 : (original62.map Setup.Block.length).sum = 1132 := by decide +kernel

column_blocks_part original63 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 8064 stop 8192
column_blocks_part target63Region6 from Verification.byteShiftColumn6 start 8064 stop 8192
noncomputable def target63 : List Setup.Block := target63Region6

theorem chunkChecked63 : normalizeSetupBlocks original63 = normalizeSetupBlocks target63 := by
  exact congrArg normalizeSetupBlocks (show original63 = target63 from rfl)

theorem chunkLength63 : (original63.map Setup.Block.length).sum = 1264 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
