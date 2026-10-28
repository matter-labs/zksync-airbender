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

column_blocks_part original57 from Data.GKRSetup.Unified.setupColumn7 start 7296 stop 7424
column_blocks_part target57Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 7296 stop 7424
noncomputable def target57 : List Setup.Block := target57Region6

theorem chunkSame57 : original57 = target57 := by rfl

theorem chunkLength57 : (original57.map Setup.Block.length).sum = 1736 := by decide +kernel

column_blocks_part original58 from Data.GKRSetup.Unified.setupColumn7 start 7424 stop 7552
column_blocks_part target58Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 7424 stop 7552
noncomputable def target58 : List Setup.Block := target58Region6

theorem chunkSame58 : original58 = target58 := by rfl

theorem chunkLength58 : (original58.map Setup.Block.length).sum = 1528 := by decide +kernel

column_blocks_part original59 from Data.GKRSetup.Unified.setupColumn7 start 7552 stop 7680
column_blocks_part target59Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 7552 stop 7680
noncomputable def target59 : List Setup.Block := target59Region6

theorem chunkSame59 : original59 = target59 := by rfl

theorem chunkLength59 : (original59.map Setup.Block.length).sum = 1520 := by decide +kernel

column_blocks_part original60 from Data.GKRSetup.Unified.setupColumn7 start 7680 stop 7808
column_blocks_part target60Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 7680 stop 7808
noncomputable def target60 : List Setup.Block := target60Region6

theorem chunkSame60 : original60 = target60 := by rfl

theorem chunkLength60 : (original60.map Setup.Block.length).sum = 1344 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
