import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original1 from Data.GKRSetup.Unified.setupColumn2 start 128 stop 256
column_blocks_part target1Region13 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 111 stop 239
noncomputable def target1 : List Setup.Block := target1Region13

theorem chunkSame1 : original1 = target1 := by rfl

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 2360 := by decide +kernel

column_blocks_part original2 from Data.GKRSetup.Unified.setupColumn2 start 256 stop 384
column_blocks_part target2Region13 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 239 stop 367
noncomputable def target2 : List Setup.Block := target2Region13

theorem chunkSame2 : original2 = target2 := by rfl

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part original3 from Data.GKRSetup.Unified.setupColumn2 start 384 stop 512
column_blocks_part target3Region13 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 367 stop 495
noncomputable def target3 : List Setup.Block := target3Region13

theorem chunkSame3 : original3 = target3 := by rfl

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 14560 := by decide +kernel

column_blocks_part original4 from Data.GKRSetup.Unified.setupColumn2 start 512 stop 640
column_blocks_part target4Region13 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 495 stop 623
noncomputable def target4 : List Setup.Block := target4Region13

theorem chunkSame4 : original4 = target4 := by rfl

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 4840 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column2
