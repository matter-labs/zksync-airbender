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

column_blocks_part original33 from Data.GKRSetup.Unified.setupColumn7 start 4224 stop 4352
column_blocks_part target33Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 4224 stop 4352
noncomputable def target33 : List Setup.Block := target33Region6

theorem chunkSame33 : original33 = target33 := by rfl

theorem chunkLength33 : (original33.map Setup.Block.length).sum = 1200 := by decide +kernel

column_blocks_part original34 from Data.GKRSetup.Unified.setupColumn7 start 4352 stop 4480
column_blocks_part target34Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 4352 stop 4480
noncomputable def target34 : List Setup.Block := target34Region6

theorem chunkSame34 : original34 = target34 := by rfl

theorem chunkLength34 : (original34.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original35 from Data.GKRSetup.Unified.setupColumn7 start 4480 stop 4608
column_blocks_part target35Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 4480 stop 4608
noncomputable def target35 : List Setup.Block := target35Region6

theorem chunkSame35 : original35 = target35 := by rfl

theorem chunkLength35 : (original35.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part original36 from Data.GKRSetup.Unified.setupColumn7 start 4608 stop 4736
column_blocks_part target36Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 4608 stop 4736
noncomputable def target36 : List Setup.Block := target36Region6

theorem chunkSame36 : original36 = target36 := by rfl

theorem chunkLength36 : (original36.map Setup.Block.length).sum = 1048 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
