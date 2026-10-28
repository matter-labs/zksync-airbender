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

column_blocks_part original133 from Data.GKRSetup.Unified.setupColumn5 start 17024 stop 17152
column_blocks_part target133Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 17024 stop 17152
noncomputable def target133 : List Setup.Block := target133Region6

theorem chunkSame133 : original133 = target133 := by rfl

theorem chunkLength133 : (original133.map Setup.Block.length).sum = 1200 := by decide +kernel

column_blocks_part original134 from Data.GKRSetup.Unified.setupColumn5 start 17152 stop 17280
column_blocks_part target134Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 17152 stop 17280
noncomputable def target134 : List Setup.Block := target134Region6

theorem chunkSame134 : original134 = target134 := by rfl

theorem chunkLength134 : (original134.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original135 from Data.GKRSetup.Unified.setupColumn5 start 17280 stop 17408
column_blocks_part target135Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 17280 stop 17408
noncomputable def target135 : List Setup.Block := target135Region6

theorem chunkSame135 : original135 = target135 := by rfl

theorem chunkLength135 : (original135.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original136 from Data.GKRSetup.Unified.setupColumn5 start 17408 stop 17536
column_blocks_part target136Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 17408 stop 17536
noncomputable def target136 : List Setup.Block := target136Region6

theorem chunkSame136 : original136 = target136 := by rfl

theorem chunkLength136 : (original136.map Setup.Block.length).sum = 1056 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
