import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original189 from Data.GKRSetup.Unified.setupColumn4 start 24192 stop 24320
column_blocks_part target189Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24192 stop 24320
noncomputable def target189 : List Setup.Block := target189Region6

theorem chunkSame189 : original189 = target189 := by rfl

theorem chunkLength189 : (original189.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original191 from Data.GKRSetup.Unified.setupColumn4 start 24448 stop 24576
column_blocks_part target191Region8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 34 stop 162
noncomputable def target191 : List Setup.Block := target191Region8

theorem chunkSame191 : original191 = target191 := by rfl

theorem chunkLength191 : (original191.map Setup.Block.length).sum = 12560 := by decide +kernel

column_blocks_part original192 from Data.GKRSetup.Unified.setupColumn4 start 24576 stop 24704
column_blocks_part target192Region8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 162 stop 290
noncomputable def target192 : List Setup.Block := target192Region8

theorem chunkSame192 : original192 = target192 := by rfl

theorem chunkLength192 : (original192.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original193 from Data.GKRSetup.Unified.setupColumn4 start 24704 stop 24832
column_blocks_part target193Region8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 290 stop 418
noncomputable def target193 : List Setup.Block := target193Region8

theorem chunkSame193 : original193 = target193 := by rfl

theorem chunkLength193 : (original193.map Setup.Block.length).sum = 6400 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
