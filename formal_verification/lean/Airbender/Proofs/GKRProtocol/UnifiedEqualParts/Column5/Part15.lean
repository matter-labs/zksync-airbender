import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original61 from Data.GKRSetup.Unified.setupColumn5 start 7808 stop 7936
column_blocks_part target61Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 7808 stop 7936
noncomputable def target61 : List Setup.Block := target61Region6

theorem chunkSame61 : original61 = target61 := by rfl

theorem chunkLength61 : (original61.map Setup.Block.length).sum = 2272 := by decide +kernel

column_blocks_part original62 from Data.GKRSetup.Unified.setupColumn5 start 7936 stop 8064
column_blocks_part target62Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 7936 stop 8064
noncomputable def target62 : List Setup.Block := target62Region6

theorem chunkSame62 : original62 = target62 := by rfl

theorem chunkLength62 : (original62.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original63 from Data.GKRSetup.Unified.setupColumn5 start 8064 stop 8192
column_blocks_part target63Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 8064 stop 8192
noncomputable def target63 : List Setup.Block := target63Region6

theorem chunkSame63 : original63 = target63 := by rfl

theorem chunkLength63 : (original63.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part original64 from Data.GKRSetup.Unified.setupColumn5 start 8192 stop 8320
column_blocks_part target64Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 8192 stop 8320
noncomputable def target64 : List Setup.Block := target64Region6

theorem chunkSame64 : original64 = target64 := by rfl

theorem chunkLength64 : (original64.map Setup.Block.length).sum = 2080 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
