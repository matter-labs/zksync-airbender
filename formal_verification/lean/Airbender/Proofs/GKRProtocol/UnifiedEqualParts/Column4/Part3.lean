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

column_blocks_part original13 from Data.GKRSetup.Unified.setupColumn4 start 1664 stop 1792
column_blocks_part target13Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 1664 stop 1792
noncomputable def target13 : List Setup.Block := target13Region6

theorem chunkSame13 : original13 = target13 := by rfl

theorem chunkLength13 : (original13.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original14 from Data.GKRSetup.Unified.setupColumn4 start 1792 stop 1920
column_blocks_part target14Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 1792 stop 1920
noncomputable def target14 : List Setup.Block := target14Region6

theorem chunkSame14 : original14 = target14 := by rfl

theorem chunkLength14 : (original14.map Setup.Block.length).sum = 2264 := by decide +kernel

column_blocks_part original15 from Data.GKRSetup.Unified.setupColumn4 start 1920 stop 2048
column_blocks_part target15Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 1920 stop 2048
noncomputable def target15 : List Setup.Block := target15Region6

theorem chunkSame15 : original15 = target15 := by rfl

theorem chunkLength15 : (original15.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part original16 from Data.GKRSetup.Unified.setupColumn4 start 2048 stop 2176
column_blocks_part target16Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 2048 stop 2176
noncomputable def target16 : List Setup.Block := target16Region6

theorem chunkSame16 : original16 = target16 := by rfl

theorem chunkLength16 : (original16.map Setup.Block.length).sum = 2048 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
