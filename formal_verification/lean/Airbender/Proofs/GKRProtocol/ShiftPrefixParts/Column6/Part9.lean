import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original72 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 9216 stop 9344
column_blocks_part target72Region6 from Verification.byteShiftColumn6 start 9216 stop 9344
noncomputable def target72 : List Setup.Block := target72Region6

theorem chunkChecked72 : normalizeSetupBlocks original72 = normalizeSetupBlocks target72 := by
  exact congrArg normalizeSetupBlocks (show original72 = target72 from rfl)

theorem chunkLength72 : (original72.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original73 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 9344 stop 9472
column_blocks_part target73Region6 from Verification.byteShiftColumn6 start 9344 stop 9472
noncomputable def target73 : List Setup.Block := target73Region6

theorem chunkChecked73 : normalizeSetupBlocks original73 = normalizeSetupBlocks target73 := by
  exact congrArg normalizeSetupBlocks (show original73 = target73 from rfl)

theorem chunkLength73 : (original73.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original74 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 9472 stop 9600
column_blocks_part target74Region6 from Verification.byteShiftColumn6 start 9472 stop 9600
noncomputable def target74 : List Setup.Block := target74Region6

theorem chunkChecked74 : normalizeSetupBlocks original74 = normalizeSetupBlocks target74 := by
  exact congrArg normalizeSetupBlocks (show original74 = target74 from rfl)

theorem chunkLength74 : (original74.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original75 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 9600 stop 9728
column_blocks_part target75Region6 from Verification.byteShiftColumn6 start 9600 stop 9728
noncomputable def target75 : List Setup.Block := target75Region6

theorem chunkChecked75 : normalizeSetupBlocks original75 = normalizeSetupBlocks target75 := by
  exact congrArg normalizeSetupBlocks (show original75 = target75 from rfl)

theorem chunkLength75 : (original75.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original76 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 9728 stop 9856
column_blocks_part target76Region6 from Verification.byteShiftColumn6 start 9728 stop 9856
noncomputable def target76 : List Setup.Block := target76Region6

theorem chunkChecked76 : normalizeSetupBlocks original76 = normalizeSetupBlocks target76 := by
  exact congrArg normalizeSetupBlocks (show original76 = target76 from rfl)

theorem chunkLength76 : (original76.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original77 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 9856 stop 9984
column_blocks_part target77Region6 from Verification.byteShiftColumn6 start 9856 stop 9984
noncomputable def target77 : List Setup.Block := target77Region6

theorem chunkChecked77 : normalizeSetupBlocks original77 = normalizeSetupBlocks target77 := by
  exact congrArg normalizeSetupBlocks (show original77 = target77 from rfl)

theorem chunkLength77 : (original77.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original78 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 9984 stop 10112
column_blocks_part target78Region6 from Verification.byteShiftColumn6 start 9984 stop 10112
noncomputable def target78 : List Setup.Block := target78Region6

theorem chunkChecked78 : normalizeSetupBlocks original78 = normalizeSetupBlocks target78 := by
  exact congrArg normalizeSetupBlocks (show original78 = target78 from rfl)

theorem chunkLength78 : (original78.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original79 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 10112 stop 10240
column_blocks_part target79Region6 from Verification.byteShiftColumn6 start 10112 stop 10240
noncomputable def target79 : List Setup.Block := target79Region6

theorem chunkChecked79 : normalizeSetupBlocks original79 = normalizeSetupBlocks target79 := by
  exact congrArg normalizeSetupBlocks (show original79 = target79 from rfl)

theorem chunkLength79 : (original79.map Setup.Block.length).sum = 1240 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
