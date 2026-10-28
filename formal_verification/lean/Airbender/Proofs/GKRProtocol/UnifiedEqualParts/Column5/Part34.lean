import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original137 from Data.GKRSetup.Unified.setupColumn5 start 17536 stop 17664
column_blocks_part target137Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 17536 stop 17664
noncomputable def target137 : List Setup.Block := target137Region6

theorem chunkSame137 : original137 = target137 := by rfl

theorem chunkLength137 : (original137.map Setup.Block.length).sum = 1176 := by decide +kernel

column_blocks_part original138 from Data.GKRSetup.Unified.setupColumn5 start 17664 stop 17792
column_blocks_part target138Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 17664 stop 17792
noncomputable def target138 : List Setup.Block := target138Region6

theorem chunkSame138 : original138 = target138 := by rfl

theorem chunkLength138 : (original138.map Setup.Block.length).sum = 1616 := by decide +kernel

column_blocks_part original139 from Data.GKRSetup.Unified.setupColumn5 start 17792 stop 17920
column_blocks_part target139Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 17792 stop 17920
noncomputable def target139 : List Setup.Block := target139Region6

theorem chunkSame139 : original139 = target139 := by rfl

theorem chunkLength139 : (original139.map Setup.Block.length).sum = 1792 := by decide +kernel

column_blocks_part original140 from Data.GKRSetup.Unified.setupColumn5 start 17920 stop 18048
column_blocks_part target140Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 17920 stop 18048
noncomputable def target140 : List Setup.Block := target140Region6

theorem chunkSame140 : original140 = target140 := by rfl

theorem chunkLength140 : (original140.map Setup.Block.length).sum = 1576 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
