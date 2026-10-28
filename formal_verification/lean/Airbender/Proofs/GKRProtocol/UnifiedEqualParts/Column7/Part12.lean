import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original49 from Data.GKRSetup.Unified.setupColumn7 start 6272 stop 6400
column_blocks_part target49Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 6272 stop 6400
noncomputable def target49 : List Setup.Block := target49Region6

theorem chunkSame49 : original49 = target49 := by rfl

theorem chunkLength49 : (original49.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original50 from Data.GKRSetup.Unified.setupColumn7 start 6400 stop 6528
column_blocks_part target50Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 6400 stop 6528
noncomputable def target50 : List Setup.Block := target50Region6

theorem chunkSame50 : original50 = target50 := by rfl

theorem chunkLength50 : (original50.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part original51 from Data.GKRSetup.Unified.setupColumn7 start 6528 stop 6656
column_blocks_part target51Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 6528 stop 6656
noncomputable def target51 : List Setup.Block := target51Region6

theorem chunkSame51 : original51 = target51 := by rfl

theorem chunkLength51 : (original51.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original52 from Data.GKRSetup.Unified.setupColumn7 start 6656 stop 6784
column_blocks_part target52Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 6656 stop 6784
noncomputable def target52 : List Setup.Block := target52Region6

theorem chunkSame52 : original52 = target52 := by rfl

theorem chunkLength52 : (original52.map Setup.Block.length).sum = 1200 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
