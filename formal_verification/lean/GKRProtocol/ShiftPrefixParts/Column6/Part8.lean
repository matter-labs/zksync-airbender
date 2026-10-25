import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original64 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 8192 stop 8320
column_blocks_part target64Region6 from Verification.byteShiftColumn6 start 8192 stop 8320
noncomputable def target64 : List Setup.Block := target64Region6

theorem chunkChecked64 : normalizeSetupBlocks original64 = normalizeSetupBlocks target64 := by
  exact congrArg normalizeSetupBlocks (show original64 = target64 from rfl)

theorem chunkLength64 : (original64.map Setup.Block.length).sum = 1248 := by decide +kernel

column_blocks_part original65 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 8320 stop 8448
column_blocks_part target65Region6 from Verification.byteShiftColumn6 start 8320 stop 8448
noncomputable def target65 : List Setup.Block := target65Region6

theorem chunkChecked65 : normalizeSetupBlocks original65 = normalizeSetupBlocks target65 := by
  exact congrArg normalizeSetupBlocks (show original65 = target65 from rfl)

theorem chunkLength65 : (original65.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original66 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 8448 stop 8576
column_blocks_part target66Region6 from Verification.byteShiftColumn6 start 8448 stop 8576
noncomputable def target66 : List Setup.Block := target66Region6

theorem chunkChecked66 : normalizeSetupBlocks original66 = normalizeSetupBlocks target66 := by
  exact congrArg normalizeSetupBlocks (show original66 = target66 from rfl)

theorem chunkLength66 : (original66.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original67 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 8576 stop 8704
column_blocks_part target67Region6 from Verification.byteShiftColumn6 start 8576 stop 8704
noncomputable def target67 : List Setup.Block := target67Region6

theorem chunkChecked67 : normalizeSetupBlocks original67 = normalizeSetupBlocks target67 := by
  exact congrArg normalizeSetupBlocks (show original67 = target67 from rfl)

theorem chunkLength67 : (original67.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original68 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 8704 stop 8832
column_blocks_part target68Region6 from Verification.byteShiftColumn6 start 8704 stop 8832
noncomputable def target68 : List Setup.Block := target68Region6

theorem chunkChecked68 : normalizeSetupBlocks original68 = normalizeSetupBlocks target68 := by
  exact congrArg normalizeSetupBlocks (show original68 = target68 from rfl)

theorem chunkLength68 : (original68.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original69 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 8832 stop 8960
column_blocks_part target69Region6 from Verification.byteShiftColumn6 start 8832 stop 8960
noncomputable def target69 : List Setup.Block := target69Region6

theorem chunkChecked69 : normalizeSetupBlocks original69 = normalizeSetupBlocks target69 := by
  exact congrArg normalizeSetupBlocks (show original69 = target69 from rfl)

theorem chunkLength69 : (original69.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original70 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 8960 stop 9088
column_blocks_part target70Region6 from Verification.byteShiftColumn6 start 8960 stop 9088
noncomputable def target70 : List Setup.Block := target70Region6

theorem chunkChecked70 : normalizeSetupBlocks original70 = normalizeSetupBlocks target70 := by
  exact congrArg normalizeSetupBlocks (show original70 = target70 from rfl)

theorem chunkLength70 : (original70.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original71 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 9088 stop 9216
column_blocks_part target71Region6 from Verification.byteShiftColumn6 start 9088 stop 9216
noncomputable def target71 : List Setup.Block := target71Region6

theorem chunkChecked71 : normalizeSetupBlocks original71 = normalizeSetupBlocks target71 := by
  exact congrArg normalizeSetupBlocks (show original71 = target71 from rfl)

theorem chunkLength71 : (original71.map Setup.Block.length).sum = 1240 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
