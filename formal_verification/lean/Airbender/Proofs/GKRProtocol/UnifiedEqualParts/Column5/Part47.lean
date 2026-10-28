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

column_blocks_part original189 from Data.GKRSetup.Unified.setupColumn5 start 24192 stop 24320
column_blocks_part target189Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24192 stop 24320
noncomputable def target189 : List Setup.Block := target189Region6

theorem chunkSame189 : original189 = target189 := by rfl

theorem chunkLength189 : (original189.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part original190 from Data.GKRSetup.Unified.setupColumn5 start 24320 stop 24448
column_blocks_part target190Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24320 stop 24448
noncomputable def target190 : List Setup.Block := target190Region6

theorem chunkSame190 : original190 = target190 := by rfl

theorem chunkLength190 : (original190.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original192 from Data.GKRSetup.Unified.setupColumn5 start 24576 stop 24704
column_blocks_part target192Region10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 16 stop 144
noncomputable def target192 : List Setup.Block := target192Region10

theorem chunkSame192 : original192 = target192 := by rfl

theorem chunkLength192 : (original192.map Setup.Block.length).sum = 16640 := by decide +kernel

column_blocks_part original193 from Data.GKRSetup.Unified.setupColumn5 start 24704 stop 24832
column_blocks_part target193Region10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 144 stop 272
noncomputable def target193 : List Setup.Block := target193Region10

theorem chunkSame193 : original193 = target193 := by rfl

theorem chunkLength193 : (original193.map Setup.Block.length).sum = 1400 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
