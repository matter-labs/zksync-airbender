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

column_blocks_part original17 from Data.GKRSetup.Unified.setupColumn6 start 2176 stop 2304
column_blocks_part target17Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 2176 stop 2304
noncomputable def target17 : List Setup.Block := target17Region6

theorem chunkSame17 : original17 = target17 := by rfl

theorem chunkLength17 : (original17.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part original18 from Data.GKRSetup.Unified.setupColumn6 start 2304 stop 2432
column_blocks_part target18Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 2304 stop 2432
noncomputable def target18 : List Setup.Block := target18Region6

theorem chunkSame18 : original18 = target18 := by rfl

theorem chunkLength18 : (original18.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original19 from Data.GKRSetup.Unified.setupColumn6 start 2432 stop 2560
column_blocks_part target19Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 2432 stop 2560
noncomputable def target19 : List Setup.Block := target19Region6

theorem chunkSame19 : original19 = target19 := by rfl

theorem chunkLength19 : (original19.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original20 from Data.GKRSetup.Unified.setupColumn6 start 2560 stop 2688
column_blocks_part target20Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 2560 stop 2688
noncomputable def target20 : List Setup.Block := target20Region6

theorem chunkSame20 : original20 = target20 := by rfl

theorem chunkLength20 : (original20.map Setup.Block.length).sum = 1288 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
