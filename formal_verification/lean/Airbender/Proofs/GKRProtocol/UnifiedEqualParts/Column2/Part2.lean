import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original9 from Data.GKRSetup.Unified.setupColumn2 start 1152 stop 1280
column_blocks_part target9Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 236 stop 364
noncomputable def target9 : List Setup.Block := target9Region14

theorem chunkSame9 : original9 = target9 := by rfl

theorem chunkLength9 : (original9.map Setup.Block.length).sum = 2224 := by decide +kernel

column_blocks_part original10 from Data.GKRSetup.Unified.setupColumn2 start 1280 stop 1408
column_blocks_part target10Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 364 stop 492
noncomputable def target10 : List Setup.Block := target10Region14

theorem chunkSame10 : original10 = target10 := by rfl

theorem chunkLength10 : (original10.map Setup.Block.length).sum = 14368 := by decide +kernel

column_blocks_part original11 from Data.GKRSetup.Unified.setupColumn2 start 1408 stop 1536
column_blocks_part target11Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 492 stop 620
noncomputable def target11 : List Setup.Block := target11Region14

theorem chunkSame11 : original11 = target11 := by rfl

theorem chunkLength11 : (original11.map Setup.Block.length).sum = 5080 := by decide +kernel

column_blocks_part original12 from Data.GKRSetup.Unified.setupColumn2 start 1536 stop 1664
column_blocks_part target12Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 620 stop 748
noncomputable def target12 : List Setup.Block := target12Region14

theorem chunkSame12 : original12 = target12 := by rfl

theorem chunkLength12 : (original12.map Setup.Block.length).sum = 1352 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column2
