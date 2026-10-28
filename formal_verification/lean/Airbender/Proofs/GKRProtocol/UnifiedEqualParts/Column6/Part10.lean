import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original41 from Data.GKRSetup.Unified.setupColumn6 start 5248 stop 5376
column_blocks_part target41Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 5248 stop 5376
noncomputable def target41 : List Setup.Block := target41Region6

theorem chunkSame41 : original41 = target41 := by rfl

theorem chunkLength41 : (original41.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original42 from Data.GKRSetup.Unified.setupColumn6 start 5376 stop 5504
column_blocks_part target42Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 5376 stop 5504
noncomputable def target42 : List Setup.Block := target42Region6

theorem chunkSame42 : original42 = target42 := by rfl

theorem chunkLength42 : (original42.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original43 from Data.GKRSetup.Unified.setupColumn6 start 5504 stop 5632
column_blocks_part target43Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 5504 stop 5632
noncomputable def target43 : List Setup.Block := target43Region6

theorem chunkSame43 : original43 = target43 := by rfl

theorem chunkLength43 : (original43.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original44 from Data.GKRSetup.Unified.setupColumn6 start 5632 stop 5760
column_blocks_part target44Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 5632 stop 5760
noncomputable def target44 : List Setup.Block := target44Region6

theorem chunkSame44 : original44 = target44 := by rfl

theorem chunkLength44 : (original44.map Setup.Block.length).sum = 1080 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
