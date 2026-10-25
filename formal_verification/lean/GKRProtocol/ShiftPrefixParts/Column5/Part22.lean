import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original176 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 22528 stop 22656
column_blocks_part target176Region6 from Verification.byteShiftColumn5 start 22528 stop 22656
noncomputable def target176 : List Setup.Block := target176Region6

theorem chunkChecked176 : normalizeSetupBlocks original176 = normalizeSetupBlocks target176 := by
  exact congrArg normalizeSetupBlocks (show original176 = target176 from rfl)

theorem chunkLength176 : (original176.map Setup.Block.length).sum = 1198 := by decide +kernel

column_blocks_part original177 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 22656 stop 22784
column_blocks_part target177Region6 from Verification.byteShiftColumn5 start 22656 stop 22784
noncomputable def target177 : List Setup.Block := target177Region6

theorem chunkChecked177 : normalizeSetupBlocks original177 = normalizeSetupBlocks target177 := by
  exact congrArg normalizeSetupBlocks (show original177 = target177 from rfl)

theorem chunkLength177 : (original177.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part original178 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 22784 stop 22912
column_blocks_part target178Region6 from Verification.byteShiftColumn5 start 22784 stop 22912
noncomputable def target178 : List Setup.Block := target178Region6

theorem chunkChecked178 : normalizeSetupBlocks original178 = normalizeSetupBlocks target178 := by
  exact congrArg normalizeSetupBlocks (show original178 = target178 from rfl)

theorem chunkLength178 : (original178.map Setup.Block.length).sum = 1129 := by decide +kernel

column_blocks_part original179 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 22912 stop 23040
column_blocks_part target179Region6 from Verification.byteShiftColumn5 start 22912 stop 23040
noncomputable def target179 : List Setup.Block := target179Region6

theorem chunkChecked179 : normalizeSetupBlocks original179 = normalizeSetupBlocks target179 := by
  exact congrArg normalizeSetupBlocks (show original179 = target179 from rfl)

theorem chunkLength179 : (original179.map Setup.Block.length).sum = 1153 := by decide +kernel

column_blocks_part original180 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 23040 stop 23168
column_blocks_part target180Region6 from Verification.byteShiftColumn5 start 23040 stop 23168
noncomputable def target180 : List Setup.Block := target180Region6

theorem chunkChecked180 : normalizeSetupBlocks original180 = normalizeSetupBlocks target180 := by
  exact congrArg normalizeSetupBlocks (show original180 = target180 from rfl)

theorem chunkLength180 : (original180.map Setup.Block.length).sum = 1079 := by decide +kernel

column_blocks_part original181 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 23168 stop 23296
column_blocks_part target181Region6 from Verification.byteShiftColumn5 start 23168 stop 23296
noncomputable def target181 : List Setup.Block := target181Region6

theorem chunkChecked181 : normalizeSetupBlocks original181 = normalizeSetupBlocks target181 := by
  exact congrArg normalizeSetupBlocks (show original181 = target181 from rfl)

theorem chunkLength181 : (original181.map Setup.Block.length).sum = 1199 := by decide +kernel

column_blocks_part original182 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 23296 stop 23424
column_blocks_part target182Region6 from Verification.byteShiftColumn5 start 23296 stop 23424
noncomputable def target182 : List Setup.Block := target182Region6

theorem chunkChecked182 : normalizeSetupBlocks original182 = normalizeSetupBlocks target182 := by
  exact congrArg normalizeSetupBlocks (show original182 = target182 from rfl)

theorem chunkLength182 : (original182.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part original183 from Data.GKRSetup.ShiftBinop.setupColumn5
  start 23424 stop 23552
column_blocks_part target183Region6 from Verification.byteShiftColumn5 start 23424 stop 23552
noncomputable def target183 : List Setup.Block := target183Region6

theorem chunkChecked183 : normalizeSetupBlocks original183 = normalizeSetupBlocks target183 := by
  exact congrArg normalizeSetupBlocks (show original183 = target183 from rfl)

theorem chunkLength183 : (original183.map Setup.Block.length).sum = 1129 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column5
