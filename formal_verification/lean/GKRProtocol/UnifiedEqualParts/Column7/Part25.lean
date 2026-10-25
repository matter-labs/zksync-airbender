import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original101 from Data.GKRSetup.Unified.setupColumn7 start 12928 stop 13056
column_blocks_part target101Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 12928 stop 13056
noncomputable def target101 : List Setup.Block := target101Region6

theorem chunkSame101 : original101 = target101 := by rfl

theorem chunkLength101 : (original101.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original102 from Data.GKRSetup.Unified.setupColumn7 start 13056 stop 13184
column_blocks_part target102Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 13056 stop 13184
noncomputable def target102 : List Setup.Block := target102Region6

theorem chunkSame102 : original102 = target102 := by rfl

theorem chunkLength102 : (original102.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original103 from Data.GKRSetup.Unified.setupColumn7 start 13184 stop 13312
column_blocks_part target103Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 13184 stop 13312
noncomputable def target103 : List Setup.Block := target103Region6

theorem chunkSame103 : original103 = target103 := by rfl

theorem chunkLength103 : (original103.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original104 from Data.GKRSetup.Unified.setupColumn7 start 13312 stop 13440
column_blocks_part target104Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 13312 stop 13440
noncomputable def target104 : List Setup.Block := target104Region6

theorem chunkSame104 : original104 = target104 := by rfl

theorem chunkLength104 : (original104.map Setup.Block.length).sum = 1232 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
