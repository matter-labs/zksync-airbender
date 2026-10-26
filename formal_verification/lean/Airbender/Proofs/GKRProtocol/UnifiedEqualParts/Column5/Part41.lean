import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original165 from Data.GKRSetup.Unified.setupColumn5 start 21120 stop 21248
column_blocks_part target165Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 21120 stop 21248
noncomputable def target165 : List Setup.Block := target165Region6

theorem chunkSame165 : original165 = target165 := by rfl

theorem chunkLength165 : (original165.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original166 from Data.GKRSetup.Unified.setupColumn5 start 21248 stop 21376
column_blocks_part target166Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 21248 stop 21376
noncomputable def target166 : List Setup.Block := target166Region6

theorem chunkSame166 : original166 = target166 := by rfl

theorem chunkLength166 : (original166.map Setup.Block.length).sum = 1214 := by decide +kernel

column_blocks_part original167 from Data.GKRSetup.Unified.setupColumn5 start 21376 stop 21504
column_blocks_part target167Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 21376 stop 21504
noncomputable def target167 : List Setup.Block := target167Region6

theorem chunkSame167 : original167 = target167 := by rfl

theorem chunkLength167 : (original167.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original168 from Data.GKRSetup.Unified.setupColumn5 start 21504 stop 21632
column_blocks_part target168Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 21504 stop 21632
noncomputable def target168 : List Setup.Block := target168Region6

theorem chunkSame168 : original168 = target168 := by rfl

theorem chunkLength168 : (original168.map Setup.Block.length).sum = 1072 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
