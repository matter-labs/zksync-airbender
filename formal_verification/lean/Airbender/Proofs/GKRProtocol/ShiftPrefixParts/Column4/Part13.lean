import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original104 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 13312 stop 13440
column_blocks_part target104Region6 from Verification.byteShiftColumn4 start 13312 stop 13440
noncomputable def target104 : List Setup.Block := target104Region6

theorem chunkChecked104 : normalizeSetupBlocks original104 = normalizeSetupBlocks target104 := by
  exact congrArg normalizeSetupBlocks (show original104 = target104 from rfl)

theorem chunkLength104 : (original104.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original105 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 13440 stop 13568
column_blocks_part target105Region6 from Verification.byteShiftColumn4 start 13440 stop 13568
noncomputable def target105 : List Setup.Block := target105Region6

theorem chunkChecked105 : normalizeSetupBlocks original105 = normalizeSetupBlocks target105 := by
  exact congrArg normalizeSetupBlocks (show original105 = target105 from rfl)

theorem chunkLength105 : (original105.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part original106 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 13568 stop 13696
column_blocks_part target106Region6 from Verification.byteShiftColumn4 start 13568 stop 13696
noncomputable def target106 : List Setup.Block := target106Region6

theorem chunkChecked106 : normalizeSetupBlocks original106 = normalizeSetupBlocks target106 := by
  exact congrArg normalizeSetupBlocks (show original106 = target106 from rfl)

theorem chunkLength106 : (original106.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part original107 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 13696 stop 13824
column_blocks_part target107Region6 from Verification.byteShiftColumn4 start 13696 stop 13824
noncomputable def target107 : List Setup.Block := target107Region6

theorem chunkChecked107 : normalizeSetupBlocks original107 = normalizeSetupBlocks target107 := by
  exact congrArg normalizeSetupBlocks (show original107 = target107 from rfl)

theorem chunkLength107 : (original107.map Setup.Block.length).sum = 1224 := by decide +kernel

column_blocks_part original108 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 13824 stop 13952
column_blocks_part target108Region6 from Verification.byteShiftColumn4 start 13824 stop 13952
noncomputable def target108 : List Setup.Block := target108Region6

theorem chunkChecked108 : normalizeSetupBlocks original108 = normalizeSetupBlocks target108 := by
  exact congrArg normalizeSetupBlocks (show original108 = target108 from rfl)

theorem chunkLength108 : (original108.map Setup.Block.length).sum = 1088 := by decide +kernel

column_blocks_part original109 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 13952 stop 14080
column_blocks_part target109Region6 from Verification.byteShiftColumn4 start 13952 stop 14080
noncomputable def target109 : List Setup.Block := target109Region6

theorem chunkChecked109 : normalizeSetupBlocks original109 = normalizeSetupBlocks target109 := by
  exact congrArg normalizeSetupBlocks (show original109 = target109 from rfl)

theorem chunkLength109 : (original109.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part original110 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 14080 stop 14208
column_blocks_part target110Region6 from Verification.byteShiftColumn4 start 14080 stop 14208
noncomputable def target110 : List Setup.Block := target110Region6

theorem chunkChecked110 : normalizeSetupBlocks original110 = normalizeSetupBlocks target110 := by
  exact congrArg normalizeSetupBlocks (show original110 = target110 from rfl)

theorem chunkLength110 : (original110.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part original111 from Data.GKRSetup.ShiftBinop.setupColumn4
  start 14208 stop 14336
column_blocks_part target111Region6 from Verification.byteShiftColumn4 start 14208 stop 14336
noncomputable def target111 : List Setup.Block := target111Region6

theorem chunkChecked111 : normalizeSetupBlocks original111 = normalizeSetupBlocks target111 := by
  exact congrArg normalizeSetupBlocks (show original111 = target111 from rfl)

theorem chunkLength111 : (original111.map Setup.Block.length).sum = 1240 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column4
