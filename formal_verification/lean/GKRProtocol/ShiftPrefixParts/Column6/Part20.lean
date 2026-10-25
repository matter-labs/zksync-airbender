import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original160 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 20480 stop 20608
column_blocks_part target160Region6 from Verification.byteShiftColumn6 start 20480 stop 20608
noncomputable def target160 : List Setup.Block := target160Region6

theorem chunkChecked160 : normalizeSetupBlocks original160 = normalizeSetupBlocks target160 := by
  exact congrArg normalizeSetupBlocks (show original160 = target160 from rfl)

theorem chunkLength160 : (original160.map Setup.Block.length).sum = 1286 := by decide +kernel

column_blocks_part original161 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 20608 stop 20736
column_blocks_part target161Region6 from Verification.byteShiftColumn6 start 20608 stop 20736
noncomputable def target161 : List Setup.Block := target161Region6

theorem chunkChecked161 : normalizeSetupBlocks original161 = normalizeSetupBlocks target161 := by
  exact congrArg normalizeSetupBlocks (show original161 = target161 from rfl)

theorem chunkLength161 : (original161.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original162 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 20736 stop 20864
column_blocks_part target162Region6 from Verification.byteShiftColumn6 start 20736 stop 20864
noncomputable def target162 : List Setup.Block := target162Region6

theorem chunkChecked162 : normalizeSetupBlocks original162 = normalizeSetupBlocks target162 := by
  exact congrArg normalizeSetupBlocks (show original162 = target162 from rfl)

theorem chunkLength162 : (original162.map Setup.Block.length).sum = 1210 := by decide +kernel

column_blocks_part original163 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 20864 stop 20992
column_blocks_part target163Region6 from Verification.byteShiftColumn6 start 20864 stop 20992
noncomputable def target163 : List Setup.Block := target163Region6

theorem chunkChecked163 : normalizeSetupBlocks original163 = normalizeSetupBlocks target163 := by
  exact congrArg normalizeSetupBlocks (show original163 = target163 from rfl)

theorem chunkLength163 : (original163.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original164 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 20992 stop 21120
column_blocks_part target164Region6 from Verification.byteShiftColumn6 start 20992 stop 21120
noncomputable def target164 : List Setup.Block := target164Region6

theorem chunkChecked164 : normalizeSetupBlocks original164 = normalizeSetupBlocks target164 := by
  exact congrArg normalizeSetupBlocks (show original164 = target164 from rfl)

theorem chunkLength164 : (original164.map Setup.Block.length).sum = 1214 := by decide +kernel

column_blocks_part original165 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 21120 stop 21248
column_blocks_part target165Region6 from Verification.byteShiftColumn6 start 21120 stop 21248
noncomputable def target165 : List Setup.Block := target165Region6

theorem chunkChecked165 : normalizeSetupBlocks original165 = normalizeSetupBlocks target165 := by
  exact congrArg normalizeSetupBlocks (show original165 = target165 from rfl)

theorem chunkLength165 : (original165.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original166 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 21248 stop 21376
column_blocks_part target166Region6 from Verification.byteShiftColumn6 start 21248 stop 21376
noncomputable def target166 : List Setup.Block := target166Region6

theorem chunkChecked166 : normalizeSetupBlocks original166 = normalizeSetupBlocks target166 := by
  exact congrArg normalizeSetupBlocks (show original166 = target166 from rfl)

theorem chunkLength166 : (original166.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part original167 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 21376 stop 21504
column_blocks_part target167Region6 from Verification.byteShiftColumn6 start 21376 stop 21504
noncomputable def target167 : List Setup.Block := target167Region6

theorem chunkChecked167 : normalizeSetupBlocks original167 = normalizeSetupBlocks target167 := by
  exact congrArg normalizeSetupBlocks (show original167 = target167 from rfl)

theorem chunkLength167 : (original167.map Setup.Block.length).sum = 1234 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
