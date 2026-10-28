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

column_blocks_part original77 from Data.GKRSetup.Unified.setupColumn7 start 9856 stop 9984
column_blocks_part target77Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 9856 stop 9984
noncomputable def target77 : List Setup.Block := target77Region6

theorem chunkSame77 : original77 = target77 := by rfl

theorem chunkLength77 : (original77.map Setup.Block.length).sum = 1112 := by decide +kernel

column_blocks_part original78 from Data.GKRSetup.Unified.setupColumn7 start 9984 stop 10112
column_blocks_part target78Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 9984 stop 10112
noncomputable def target78 : List Setup.Block := target78Region6

theorem chunkSame78 : original78 = target78 := by rfl

theorem chunkLength78 : (original78.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original79 from Data.GKRSetup.Unified.setupColumn7 start 10112 stop 10240
column_blocks_part target79Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 10112 stop 10240
noncomputable def target79 : List Setup.Block := target79Region6

theorem chunkSame79 : original79 = target79 := by rfl

theorem chunkLength79 : (original79.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original80 from Data.GKRSetup.Unified.setupColumn7 start 10240 stop 10368
column_blocks_part target80Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 10240 stop 10368
noncomputable def target80 : List Setup.Block := target80Region6

theorem chunkSame80 : original80 = target80 := by rfl

theorem chunkLength80 : (original80.map Setup.Block.length).sum = 1256 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
