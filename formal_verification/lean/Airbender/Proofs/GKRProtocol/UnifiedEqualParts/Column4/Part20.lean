import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original81 from Data.GKRSetup.Unified.setupColumn4 start 10368 stop 10496
column_blocks_part target81Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 10368 stop 10496
noncomputable def target81 : List Setup.Block := target81Region6

theorem chunkSame81 : original81 = target81 := by rfl

theorem chunkLength81 : (original81.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part original82 from Data.GKRSetup.Unified.setupColumn4 start 10496 stop 10624
column_blocks_part target82Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 10496 stop 10624
noncomputable def target82 : List Setup.Block := target82Region6

theorem chunkSame82 : original82 = target82 := by rfl

theorem chunkLength82 : (original82.map Setup.Block.length).sum = 1632 := by decide +kernel

column_blocks_part original83 from Data.GKRSetup.Unified.setupColumn4 start 10624 stop 10752
column_blocks_part target83Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 10624 stop 10752
noncomputable def target83 : List Setup.Block := target83Region6

theorem chunkSame83 : original83 = target83 := by rfl

theorem chunkLength83 : (original83.map Setup.Block.length).sum = 1792 := by decide +kernel

column_blocks_part original84 from Data.GKRSetup.Unified.setupColumn4 start 10752 stop 10880
column_blocks_part target84Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 10752 stop 10880
noncomputable def target84 : List Setup.Block := target84Region6

theorem chunkSame84 : original84 = target84 := by rfl

theorem chunkLength84 : (original84.map Setup.Block.length).sum = 1576 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
