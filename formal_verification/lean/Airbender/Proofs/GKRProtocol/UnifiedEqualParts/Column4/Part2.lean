import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original9 from Data.GKRSetup.Unified.setupColumn4 start 1152 stop 1280
column_blocks_part target9Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 1152 stop 1280
noncomputable def target9 : List Setup.Block := target9Region6

theorem chunkSame9 : original9 = target9 := by rfl

theorem chunkLength9 : (original9.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original10 from Data.GKRSetup.Unified.setupColumn4 start 1280 stop 1408
column_blocks_part target10Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 1280 stop 1408
noncomputable def target10 : List Setup.Block := target10Region6

theorem chunkSame10 : original10 = target10 := by rfl

theorem chunkLength10 : (original10.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part original11 from Data.GKRSetup.Unified.setupColumn4 start 1408 stop 1536
column_blocks_part target11Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 1408 stop 1536
noncomputable def target11 : List Setup.Block := target11Region6

theorem chunkSame11 : original11 = target11 := by rfl

theorem chunkLength11 : (original11.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original12 from Data.GKRSetup.Unified.setupColumn4 start 1536 stop 1664
column_blocks_part target12Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 1536 stop 1664
noncomputable def target12 : List Setup.Block := target12Region6

theorem chunkSame12 : original12 = target12 := by rfl

theorem chunkLength12 : (original12.map Setup.Block.length).sum = 2272 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
