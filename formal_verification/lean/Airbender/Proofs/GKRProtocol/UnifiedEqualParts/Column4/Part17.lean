import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original69 from Data.GKRSetup.Unified.setupColumn4 start 8832 stop 8960
column_blocks_part target69Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 8832 stop 8960
noncomputable def target69 : List Setup.Block := target69Region6

theorem chunkSame69 : original69 = target69 := by rfl

theorem chunkLength69 : (original69.map Setup.Block.length).sum = 1224 := by decide +kernel

column_blocks_part original70 from Data.GKRSetup.Unified.setupColumn4 start 8960 stop 9088
column_blocks_part target70Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 8960 stop 9088
noncomputable def target70 : List Setup.Block := target70Region6

theorem chunkSame70 : original70 = target70 := by rfl

theorem chunkLength70 : (original70.map Setup.Block.length).sum = 1088 := by decide +kernel

column_blocks_part original71 from Data.GKRSetup.Unified.setupColumn4 start 9088 stop 9216
column_blocks_part target71Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 9088 stop 9216
noncomputable def target71 : List Setup.Block := target71Region6

theorem chunkSame71 : original71 = target71 := by rfl

theorem chunkLength71 : (original71.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part original72 from Data.GKRSetup.Unified.setupColumn4 start 9216 stop 9344
column_blocks_part target72Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 9216 stop 9344
noncomputable def target72 : List Setup.Block := target72Region6

theorem chunkSame72 : original72 = target72 := by rfl

theorem chunkLength72 : (original72.map Setup.Block.length).sum = 1248 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
