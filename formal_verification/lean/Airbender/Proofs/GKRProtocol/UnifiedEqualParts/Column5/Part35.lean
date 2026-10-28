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

column_blocks_part original141 from Data.GKRSetup.Unified.setupColumn5 start 18048 stop 18176
column_blocks_part target141Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 18048 stop 18176
noncomputable def target141 : List Setup.Block := target141Region6

theorem chunkSame141 : original141 = target141 := by rfl

theorem chunkLength141 : (original141.map Setup.Block.length).sum = 1504 := by decide +kernel

column_blocks_part original142 from Data.GKRSetup.Unified.setupColumn5 start 18176 stop 18304
column_blocks_part target142Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 18176 stop 18304
noncomputable def target142 : List Setup.Block := target142Region6

theorem chunkSame142 : original142 = target142 := by rfl

theorem chunkLength142 : (original142.map Setup.Block.length).sum = 1520 := by decide +kernel

column_blocks_part original143 from Data.GKRSetup.Unified.setupColumn5 start 18304 stop 18432
column_blocks_part target143Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 18304 stop 18432
noncomputable def target143 : List Setup.Block := target143Region6

theorem chunkSame143 : original143 = target143 := by rfl

theorem chunkLength143 : (original143.map Setup.Block.length).sum = 1352 := by decide +kernel

column_blocks_part original144 from Data.GKRSetup.Unified.setupColumn5 start 18432 stop 18560
column_blocks_part target144Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 18432 stop 18560
noncomputable def target144 : List Setup.Block := target144Region6

theorem chunkSame144 : original144 = target144 := by rfl

theorem chunkLength144 : (original144.map Setup.Block.length).sum = 1456 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
