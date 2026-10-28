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

column_blocks_part original73 from Data.GKRSetup.Unified.setupColumn7 start 9344 stop 9472
column_blocks_part target73Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 9344 stop 9472
noncomputable def target73 : List Setup.Block := target73Region6

theorem chunkSame73 : original73 = target73 := by rfl

theorem chunkLength73 : (original73.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part original74 from Data.GKRSetup.Unified.setupColumn7 start 9472 stop 9600
column_blocks_part target74Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 9472 stop 9600
noncomputable def target74 : List Setup.Block := target74Region6

theorem chunkSame74 : original74 = target74 := by rfl

theorem chunkLength74 : (original74.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original75 from Data.GKRSetup.Unified.setupColumn7 start 9600 stop 9728
column_blocks_part target75Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 9600 stop 9728
noncomputable def target75 : List Setup.Block := target75Region6

theorem chunkSame75 : original75 = target75 := by rfl

theorem chunkLength75 : (original75.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original76 from Data.GKRSetup.Unified.setupColumn7 start 9728 stop 9856
column_blocks_part target76Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 9728 stop 9856
noncomputable def target76 : List Setup.Block := target76Region6

theorem chunkSame76 : original76 = target76 := by rfl

theorem chunkLength76 : (original76.map Setup.Block.length).sum = 1288 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
