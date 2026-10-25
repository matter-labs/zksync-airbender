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

column_blocks_part original129 from Data.GKRSetup.Unified.setupColumn7 start 16512 stop 16640
column_blocks_part target129Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 16512 stop 16640
noncomputable def target129 : List Setup.Block := target129Region6

theorem chunkSame129 : original129 = target129 := by rfl

theorem chunkLength129 : (original129.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part original130 from Data.GKRSetup.Unified.setupColumn7 start 16640 stop 16768
column_blocks_part target130Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 16640 stop 16768
noncomputable def target130 : List Setup.Block := target130Region6

theorem chunkSame130 : original130 = target130 := by rfl

theorem chunkLength130 : (original130.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original131 from Data.GKRSetup.Unified.setupColumn7 start 16768 stop 16896
column_blocks_part target131Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 16768 stop 16896
noncomputable def target131 : List Setup.Block := target131Region6

theorem chunkSame131 : original131 = target131 := by rfl

theorem chunkLength131 : (original131.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original132 from Data.GKRSetup.Unified.setupColumn7 start 16896 stop 17024
column_blocks_part target132Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 16896 stop 17024
noncomputable def target132 : List Setup.Block := target132Region6

theorem chunkSame132 : original132 = target132 := by rfl

theorem chunkLength132 : (original132.map Setup.Block.length).sum = 1256 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
