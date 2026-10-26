import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original157 from Data.GKRSetup.Unified.setupColumn7 start 20096 stop 20224
column_blocks_part target157Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 20096 stop 20224
noncomputable def target157 : List Setup.Block := target157Region6

theorem chunkSame157 : original157 = target157 := by rfl

theorem chunkLength157 : (original157.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part original158 from Data.GKRSetup.Unified.setupColumn7 start 20224 stop 20352
column_blocks_part target158Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 20224 stop 20352
noncomputable def target158 : List Setup.Block := target158Region6

theorem chunkSame158 : original158 = target158 := by rfl

theorem chunkLength158 : (original158.map Setup.Block.length).sum = 1088 := by decide +kernel

column_blocks_part original159 from Data.GKRSetup.Unified.setupColumn7 start 20352 stop 20480
column_blocks_part target159Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 20352 stop 20480
noncomputable def target159 : List Setup.Block := target159Region6

theorem chunkSame159 : original159 = target159 := by rfl

theorem chunkLength159 : (original159.map Setup.Block.length).sum = 1224 := by decide +kernel

column_blocks_part original160 from Data.GKRSetup.Unified.setupColumn7 start 20480 stop 20608
column_blocks_part target160Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 20480 stop 20608
noncomputable def target160 : List Setup.Block := target160Region6

theorem chunkSame160 : original160 = target160 := by rfl

theorem chunkLength160 : (original160.map Setup.Block.length).sum = 2274 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
