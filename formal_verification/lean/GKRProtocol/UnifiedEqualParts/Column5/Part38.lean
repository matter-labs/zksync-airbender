import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original153 from Data.GKRSetup.Unified.setupColumn5 start 19584 stop 19712
column_blocks_part target153Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 19584 stop 19712
noncomputable def target153 : List Setup.Block := target153Region6

theorem chunkSame153 : original153 = target153 := by rfl

theorem chunkLength153 : (original153.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original154 from Data.GKRSetup.Unified.setupColumn5 start 19712 stop 19840
column_blocks_part target154Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 19712 stop 19840
noncomputable def target154 : List Setup.Block := target154Region6

theorem chunkSame154 : original154 = target154 := by rfl

theorem chunkLength154 : (original154.map Setup.Block.length).sum = 1272 := by decide +kernel

column_blocks_part original155 from Data.GKRSetup.Unified.setupColumn5 start 19840 stop 19968
column_blocks_part target155Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 19840 stop 19968
noncomputable def target155 : List Setup.Block := target155Region6

theorem chunkSame155 : original155 = target155 := by rfl

theorem chunkLength155 : (original155.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original156 from Data.GKRSetup.Unified.setupColumn5 start 19968 stop 20096
column_blocks_part target156Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 19968 stop 20096
noncomputable def target156 : List Setup.Block := target156Region6

theorem chunkSame156 : original156 = target156 := by rfl

theorem chunkLength156 : (original156.map Setup.Block.length).sum = 1296 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
