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

column_blocks_part original45 from Data.GKRSetup.Unified.setupColumn7 start 5760 stop 5888
column_blocks_part target45Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 5760 stop 5888
noncomputable def target45 : List Setup.Block := target45Region6

theorem chunkSame45 : original45 = target45 := by rfl

theorem chunkLength45 : (original45.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original46 from Data.GKRSetup.Unified.setupColumn7 start 5888 stop 6016
column_blocks_part target46Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 5888 stop 6016
noncomputable def target46 : List Setup.Block := target46Region6

theorem chunkSame46 : original46 = target46 := by rfl

theorem chunkLength46 : (original46.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part original47 from Data.GKRSetup.Unified.setupColumn7 start 6016 stop 6144
column_blocks_part target47Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 6016 stop 6144
noncomputable def target47 : List Setup.Block := target47Region6

theorem chunkSame47 : original47 = target47 := by rfl

theorem chunkLength47 : (original47.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original48 from Data.GKRSetup.Unified.setupColumn7 start 6144 stop 6272
column_blocks_part target48Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 6144 stop 6272
noncomputable def target48 : List Setup.Block := target48Region6

theorem chunkSame48 : original48 = target48 := by rfl

theorem chunkLength48 : (original48.map Setup.Block.length).sum = 1200 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
