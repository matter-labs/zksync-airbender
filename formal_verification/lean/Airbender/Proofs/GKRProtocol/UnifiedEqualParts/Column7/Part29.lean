import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original117 from Data.GKRSetup.Unified.setupColumn7 start 14976 stop 15104
column_blocks_part target117Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 14976 stop 15104
noncomputable def target117 : List Setup.Block := target117Region6

theorem chunkSame117 : original117 = target117 := by rfl

theorem chunkLength117 : (original117.map Setup.Block.length).sum = 1304 := by decide +kernel

column_blocks_part original118 from Data.GKRSetup.Unified.setupColumn7 start 15104 stop 15232
column_blocks_part target118Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 15104 stop 15232
noncomputable def target118 : List Setup.Block := target118Region6

theorem chunkSame118 : original118 = target118 := by rfl

theorem chunkLength118 : (original118.map Setup.Block.length).sum = 1304 := by decide +kernel

column_blocks_part original119 from Data.GKRSetup.Unified.setupColumn7 start 15232 stop 15360
column_blocks_part target119Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 15232 stop 15360
noncomputable def target119 : List Setup.Block := target119Region6

theorem chunkSame119 : original119 = target119 := by rfl

theorem chunkLength119 : (original119.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part original120 from Data.GKRSetup.Unified.setupColumn7 start 15360 stop 15488
column_blocks_part target120Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 15360 stop 15488
noncomputable def target120 : List Setup.Block := target120Region6

theorem chunkSame120 : original120 = target120 := by rfl

theorem chunkLength120 : (original120.map Setup.Block.length).sum = 1280 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
