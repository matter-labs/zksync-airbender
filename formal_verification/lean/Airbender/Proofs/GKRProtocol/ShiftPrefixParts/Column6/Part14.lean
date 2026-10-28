import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Data.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original112 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 14336 stop 14464
column_blocks_part target112Region6 from Verification.byteShiftColumn6 start 14336 stop 14464
noncomputable def target112 : List Setup.Block := target112Region6

theorem chunkChecked112 : normalizeSetupBlocks original112 = normalizeSetupBlocks target112 := by
  exact congrArg normalizeSetupBlocks (show original112 = target112 from rfl)

theorem chunkLength112 : (original112.map Setup.Block.length).sum = 2288 := by decide +kernel

column_blocks_part original113 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 14464 stop 14592
column_blocks_part target113Region6 from Verification.byteShiftColumn6 start 14464 stop 14592
noncomputable def target113 : List Setup.Block := target113Region6

theorem chunkChecked113 : normalizeSetupBlocks original113 = normalizeSetupBlocks target113 := by
  exact congrArg normalizeSetupBlocks (show original113 = target113 from rfl)

theorem chunkLength113 : (original113.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original114 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 14592 stop 14720
column_blocks_part target114Region6 from Verification.byteShiftColumn6 start 14592 stop 14720
noncomputable def target114 : List Setup.Block := target114Region6

theorem chunkChecked114 : normalizeSetupBlocks original114 = normalizeSetupBlocks target114 := by
  exact congrArg normalizeSetupBlocks (show original114 = target114 from rfl)

theorem chunkLength114 : (original114.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part original115 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 14720 stop 14848
column_blocks_part target115Region6 from Verification.byteShiftColumn6 start 14720 stop 14848
noncomputable def target115 : List Setup.Block := target115Region6

theorem chunkChecked115 : normalizeSetupBlocks original115 = normalizeSetupBlocks target115 := by
  exact congrArg normalizeSetupBlocks (show original115 = target115 from rfl)

theorem chunkLength115 : (original115.map Setup.Block.length).sum = 2078 := by decide +kernel

column_blocks_part original116 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 14848 stop 14976
column_blocks_part target116Region6 from Verification.byteShiftColumn6 start 14848 stop 14976
noncomputable def target116 : List Setup.Block := target116Region6

theorem chunkChecked116 : normalizeSetupBlocks original116 = normalizeSetupBlocks target116 := by
  exact congrArg normalizeSetupBlocks (show original116 = target116 from rfl)

theorem chunkLength116 : (original116.map Setup.Block.length).sum = 2274 := by decide +kernel

column_blocks_part original117 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 14976 stop 15104
column_blocks_part target117Region6 from Verification.byteShiftColumn6 start 14976 stop 15104
noncomputable def target117 : List Setup.Block := target117Region6

theorem chunkChecked117 : normalizeSetupBlocks original117 = normalizeSetupBlocks target117 := by
  exact congrArg normalizeSetupBlocks (show original117 = target117 from rfl)

theorem chunkLength117 : (original117.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part original118 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 15104 stop 15232
column_blocks_part target118Region6 from Verification.byteShiftColumn6 start 15104 stop 15232
noncomputable def target118 : List Setup.Block := target118Region6

theorem chunkChecked118 : normalizeSetupBlocks original118 = normalizeSetupBlocks target118 := by
  exact congrArg normalizeSetupBlocks (show original118 = target118 from rfl)

theorem chunkLength118 : (original118.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original119 from Data.GKRSetup.ShiftBinop.setupColumn6
  start 15232 stop 15360
column_blocks_part target119Region6 from Verification.byteShiftColumn6 start 15232 stop 15360
noncomputable def target119 : List Setup.Block := target119Region6

theorem chunkChecked119 : normalizeSetupBlocks original119 = normalizeSetupBlocks target119 := by
  exact congrArg normalizeSetupBlocks (show original119 = target119 from rfl)

theorem chunkLength119 : (original119.map Setup.Block.length).sum = 2272 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column6
