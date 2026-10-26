import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original32 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 4096 stop 4224
column_blocks_part target32Region6 from Verification.byteShiftColumn6 start 4096 stop 4224
noncomputable def target32 : List Setup.Block := target32Region6

theorem chunkChecked32 : normalizeSetupBlocks original32 = normalizeSetupBlocks target32 := by
  exact congrArg normalizeSetupBlocks (show original32 = target32 from rfl)

theorem chunkLength32 : (original32.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original33 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 4224 stop 4352
column_blocks_part target33Region6 from Verification.byteShiftColumn6 start 4224 stop 4352
noncomputable def target33 : List Setup.Block := target33Region6

theorem chunkChecked33 : normalizeSetupBlocks original33 = normalizeSetupBlocks target33 := by
  exact congrArg normalizeSetupBlocks (show original33 = target33 from rfl)

theorem chunkLength33 : (original33.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original34 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 4352 stop 4480
column_blocks_part target34Region6 from Verification.byteShiftColumn6 start 4352 stop 4480
noncomputable def target34 : List Setup.Block := target34Region6

theorem chunkChecked34 : normalizeSetupBlocks original34 = normalizeSetupBlocks target34 := by
  exact congrArg normalizeSetupBlocks (show original34 = target34 from rfl)

theorem chunkLength34 : (original34.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original35 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 4480 stop 4608
column_blocks_part target35Region6 from Verification.byteShiftColumn6 start 4480 stop 4608
noncomputable def target35 : List Setup.Block := target35Region6

theorem chunkChecked35 : normalizeSetupBlocks original35 = normalizeSetupBlocks target35 := by
  exact congrArg normalizeSetupBlocks (show original35 = target35 from rfl)

theorem chunkLength35 : (original35.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original36 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 4608 stop 4736
column_blocks_part target36Region6 from Verification.byteShiftColumn6 start 4608 stop 4736
noncomputable def target36 : List Setup.Block := target36Region6

theorem chunkChecked36 : normalizeSetupBlocks original36 = normalizeSetupBlocks target36 := by
  exact congrArg normalizeSetupBlocks (show original36 = target36 from rfl)

theorem chunkLength36 : (original36.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original37 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 4736 stop 4864
column_blocks_part target37Region6 from Verification.byteShiftColumn6 start 4736 stop 4864
noncomputable def target37 : List Setup.Block := target37Region6

theorem chunkChecked37 : normalizeSetupBlocks original37 = normalizeSetupBlocks target37 := by
  exact congrArg normalizeSetupBlocks (show original37 = target37 from rfl)

theorem chunkLength37 : (original37.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original38 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 4864 stop 4992
column_blocks_part target38Region6 from Verification.byteShiftColumn6 start 4864 stop 4992
noncomputable def target38 : List Setup.Block := target38Region6

theorem chunkChecked38 : normalizeSetupBlocks original38 = normalizeSetupBlocks target38 := by
  exact congrArg normalizeSetupBlocks (show original38 = target38 from rfl)

theorem chunkLength38 : (original38.map Setup.Block.length).sum = 1248 := by decide +kernel

column_blocks_part original39 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 4992 stop 5120
column_blocks_part target39Region6 from Verification.byteShiftColumn6 start 4992 stop 5120
noncomputable def target39 : List Setup.Block := target39Region6

theorem chunkChecked39 : normalizeSetupBlocks original39 = normalizeSetupBlocks target39 := by
  exact congrArg normalizeSetupBlocks (show original39 = target39 from rfl)

theorem chunkLength39 : (original39.map Setup.Block.length).sum = 1240 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
