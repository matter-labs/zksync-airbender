import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original144 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 18432 stop 18560
column_blocks_part target144Region6 from Verification.byteShiftColumn6 start 18432 stop 18560
noncomputable def target144 : List Setup.Block := target144Region6

theorem chunkChecked144 : normalizeSetupBlocks original144 = normalizeSetupBlocks target144 := by
  exact congrArg normalizeSetupBlocks (show original144 = target144 from rfl)

theorem chunkLength144 : (original144.map Setup.Block.length).sum = 1312 := by decide +kernel

column_blocks_part original145 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 18560 stop 18688
column_blocks_part target145Region6 from Verification.byteShiftColumn6 start 18560 stop 18688
noncomputable def target145 : List Setup.Block := target145Region6

theorem chunkChecked145 : normalizeSetupBlocks original145 = normalizeSetupBlocks target145 := by
  exact congrArg normalizeSetupBlocks (show original145 = target145 from rfl)

theorem chunkLength145 : (original145.map Setup.Block.length).sum = 1456 := by decide +kernel

column_blocks_part original146 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 18688 stop 18816
column_blocks_part target146Region6 from Verification.byteShiftColumn6 start 18688 stop 18816
noncomputable def target146 : List Setup.Block := target146Region6

theorem chunkChecked146 : normalizeSetupBlocks original146 = normalizeSetupBlocks target146 := by
  exact congrArg normalizeSetupBlocks (show original146 = target146 from rfl)

theorem chunkLength146 : (original146.map Setup.Block.length).sum = 1320 := by decide +kernel

column_blocks_part original147 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 18816 stop 18944
column_blocks_part target147Region6 from Verification.byteShiftColumn6 start 18816 stop 18944
noncomputable def target147 : List Setup.Block := target147Region6

theorem chunkChecked147 : normalizeSetupBlocks original147 = normalizeSetupBlocks target147 := by
  exact congrArg normalizeSetupBlocks (show original147 = target147 from rfl)

theorem chunkLength147 : (original147.map Setup.Block.length).sum = 1320 := by decide +kernel

column_blocks_part original148 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 18944 stop 19072
column_blocks_part target148Region6 from Verification.byteShiftColumn6 start 18944 stop 19072
noncomputable def target148 : List Setup.Block := target148Region6

theorem chunkChecked148 : normalizeSetupBlocks original148 = normalizeSetupBlocks target148 := by
  exact congrArg normalizeSetupBlocks (show original148 = target148 from rfl)

theorem chunkLength148 : (original148.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original149 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 19072 stop 19200
column_blocks_part target149Region6 from Verification.byteShiftColumn6 start 19072 stop 19200
noncomputable def target149 : List Setup.Block := target149Region6

theorem chunkChecked149 : normalizeSetupBlocks original149 = normalizeSetupBlocks target149 := by
  exact congrArg normalizeSetupBlocks (show original149 = target149 from rfl)

theorem chunkLength149 : (original149.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original150 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 19200 stop 19328
column_blocks_part target150Region6 from Verification.byteShiftColumn6 start 19200 stop 19328
noncomputable def target150 : List Setup.Block := target150Region6

theorem chunkChecked150 : normalizeSetupBlocks original150 = normalizeSetupBlocks target150 := by
  exact congrArg normalizeSetupBlocks (show original150 = target150 from rfl)

theorem chunkLength150 : (original150.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part original151 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 19328 stop 19456
column_blocks_part target151Region6 from Verification.byteShiftColumn6 start 19328 stop 19456
noncomputable def target151 : List Setup.Block := target151Region6

theorem chunkChecked151 : normalizeSetupBlocks original151 = normalizeSetupBlocks target151 := by
  exact congrArg normalizeSetupBlocks (show original151 = target151 from rfl)

theorem chunkLength151 : (original151.map Setup.Block.length).sum = 1256 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
