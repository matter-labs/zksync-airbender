import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original88 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 11264 stop 11392
column_blocks_part target88Region6 from Verification.byteShiftColumn7 start 11264 stop 11392
noncomputable def target88 : List Setup.Block := target88Region6

theorem chunkChecked88 : normalizeSetupBlocks original88 = normalizeSetupBlocks target88 := by
  exact congrArg normalizeSetupBlocks (show original88 = target88 from rfl)

theorem chunkLength88 : (original88.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original89 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 11392 stop 11520
column_blocks_part target89Region6 from Verification.byteShiftColumn7 start 11392 stop 11520
noncomputable def target89 : List Setup.Block := target89Region6

theorem chunkChecked89 : normalizeSetupBlocks original89 = normalizeSetupBlocks target89 := by
  exact congrArg normalizeSetupBlocks (show original89 = target89 from rfl)

theorem chunkLength89 : (original89.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original90 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 11520 stop 11648
column_blocks_part target90Region6 from Verification.byteShiftColumn7 start 11520 stop 11648
noncomputable def target90 : List Setup.Block := target90Region6

theorem chunkChecked90 : normalizeSetupBlocks original90 = normalizeSetupBlocks target90 := by
  exact congrArg normalizeSetupBlocks (show original90 = target90 from rfl)

theorem chunkLength90 : (original90.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original91 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 11648 stop 11776
column_blocks_part target91Region6 from Verification.byteShiftColumn7 start 11648 stop 11776
noncomputable def target91 : List Setup.Block := target91Region6

theorem chunkChecked91 : normalizeSetupBlocks original91 = normalizeSetupBlocks target91 := by
  exact congrArg normalizeSetupBlocks (show original91 = target91 from rfl)

theorem chunkLength91 : (original91.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original92 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 11776 stop 11904
column_blocks_part target92Region6 from Verification.byteShiftColumn7 start 11776 stop 11904
noncomputable def target92 : List Setup.Block := target92Region6

theorem chunkChecked92 : normalizeSetupBlocks original92 = normalizeSetupBlocks target92 := by
  exact congrArg normalizeSetupBlocks (show original92 = target92 from rfl)

theorem chunkLength92 : (original92.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original93 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 11904 stop 12032
column_blocks_part target93Region6 from Verification.byteShiftColumn7 start 11904 stop 12032
noncomputable def target93 : List Setup.Block := target93Region6

theorem chunkChecked93 : normalizeSetupBlocks original93 = normalizeSetupBlocks target93 := by
  exact congrArg normalizeSetupBlocks (show original93 = target93 from rfl)

theorem chunkLength93 : (original93.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original94 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 12032 stop 12160
column_blocks_part target94Region6 from Verification.byteShiftColumn7 start 12032 stop 12160
noncomputable def target94 : List Setup.Block := target94Region6

theorem chunkChecked94 : normalizeSetupBlocks original94 = normalizeSetupBlocks target94 := by
  exact congrArg normalizeSetupBlocks (show original94 = target94 from rfl)

theorem chunkLength94 : (original94.map Setup.Block.length).sum = 1248 := by decide +kernel

column_blocks_part original95 from Data.GKRSetup.ShiftBinop.setupColumn7
  start 12160 stop 12288
column_blocks_part target95Region6 from Verification.byteShiftColumn7 start 12160 stop 12288
noncomputable def target95 : List Setup.Block := target95Region6

theorem chunkChecked95 : normalizeSetupBlocks original95 = normalizeSetupBlocks target95 := by
  exact congrArg normalizeSetupBlocks (show original95 = target95 from rfl)

theorem chunkLength95 : (original95.map Setup.Block.length).sum = 1240 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column7
