import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original13 from Data.GKRSetup.Unified.setupColumn2 start 1664 stop 1792
column_blocks_part target13Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 748 stop 876
noncomputable def target13 : List Setup.Block := target13Region14

theorem chunkSame13 : original13 = target13 := by rfl

theorem chunkLength13 : (original13.map Setup.Block.length).sum = 15200 := by decide +kernel

column_blocks_part original14 from Data.GKRSetup.Unified.setupColumn2 start 1792 stop 1920
column_blocks_part target14Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 876 stop 898
column_blocks_part target14Region15 from (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]) start 0 stop 106
noncomputable def target14 : List Setup.Block := target14Region14 ++ target14Region15

theorem chunkSame14 : original14 = target14 := by rfl

theorem chunkLength14 : (original14.map Setup.Block.length).sum = 24704 := by decide +kernel

column_blocks_part original15 from Data.GKRSetup.Unified.setupColumn2 start 1920 stop 2048
column_blocks_part target15Region15 from (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]) start 106 stop 234
noncomputable def target15 : List Setup.Block := target15Region15

theorem chunkSame15 : original15 = target15 := by rfl

theorem chunkLength15 : (original15.map Setup.Block.length).sum = 2600 := by decide +kernel

column_blocks_part original16 from Data.GKRSetup.Unified.setupColumn2 start 2048 stop 2176
column_blocks_part target16Region15 from (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]) start 234 stop 362
noncomputable def target16 : List Setup.Block := target16Region15

theorem chunkSame16 : original16 = target16 := by rfl

theorem chunkLength16 : (original16.map Setup.Block.length).sum = 2168 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column2
