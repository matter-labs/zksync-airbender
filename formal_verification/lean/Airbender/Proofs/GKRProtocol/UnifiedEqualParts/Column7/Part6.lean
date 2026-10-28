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

column_blocks_part original25 from Data.GKRSetup.Unified.setupColumn7 start 3200 stop 3328
column_blocks_part target25Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 3200 stop 3328
noncomputable def target25 : List Setup.Block := target25Region6

theorem chunkSame25 : original25 = target25 := by rfl

theorem chunkLength25 : (original25.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original26 from Data.GKRSetup.Unified.setupColumn7 start 3328 stop 3456
column_blocks_part target26Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 3328 stop 3456
noncomputable def target26 : List Setup.Block := target26Region6

theorem chunkSame26 : original26 = target26 := by rfl

theorem chunkLength26 : (original26.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part original27 from Data.GKRSetup.Unified.setupColumn7 start 3456 stop 3584
column_blocks_part target27Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 3456 stop 3584
noncomputable def target27 : List Setup.Block := target27Region6

theorem chunkSame27 : original27 = target27 := by rfl

theorem chunkLength27 : (original27.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original28 from Data.GKRSetup.Unified.setupColumn7 start 3584 stop 3712
column_blocks_part target28Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 3584 stop 3712
noncomputable def target28 : List Setup.Block := target28Region6

theorem chunkSame28 : original28 = target28 := by rfl

theorem chunkLength28 : (original28.map Setup.Block.length).sum = 1056 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
