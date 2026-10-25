import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original1 from Data.GKRSetup.Unified.setupColumn7 start 128 stop 256
column_blocks_part target1Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 128 stop 256
noncomputable def target1 : List Setup.Block := target1Region6

theorem chunkSame1 : original1 = target1 := by rfl

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 1520 := by decide +kernel

column_blocks_part original2 from Data.GKRSetup.Unified.setupColumn7 start 256 stop 384
column_blocks_part target2Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 256 stop 384
noncomputable def target2 : List Setup.Block := target2Region6

theorem chunkSame2 : original2 = target2 := by rfl

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 1328 := by decide +kernel

column_blocks_part original3 from Data.GKRSetup.Unified.setupColumn7 start 384 stop 512
column_blocks_part target3Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 384 stop 512
noncomputable def target3 : List Setup.Block := target3Region6

theorem chunkSame3 : original3 = target3 := by rfl

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 1456 := by decide +kernel

column_blocks_part original4 from Data.GKRSetup.Unified.setupColumn7 start 512 stop 640
column_blocks_part target4Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 512 stop 640
noncomputable def target4 : List Setup.Block := target4Region6

theorem chunkSame4 : original4 = target4 := by rfl

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 1320 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
