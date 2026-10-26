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

column_blocks_part original37 from Data.GKRSetup.Unified.setupColumn5 start 4736 stop 4864
column_blocks_part target37Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 4736 stop 4864
noncomputable def target37 : List Setup.Block := target37Region6

theorem chunkSame37 : original37 = target37 := by rfl

theorem chunkLength37 : (original37.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original38 from Data.GKRSetup.Unified.setupColumn5 start 4864 stop 4992
column_blocks_part target38Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 4864 stop 4992
noncomputable def target38 : List Setup.Block := target38Region6

theorem chunkSame38 : original38 = target38 := by rfl

theorem chunkLength38 : (original38.map Setup.Block.length).sum = 1248 := by decide +kernel

column_blocks_part original39 from Data.GKRSetup.Unified.setupColumn5 start 4992 stop 5120
column_blocks_part target39Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 4992 stop 5120
noncomputable def target39 : List Setup.Block := target39Region6

theorem chunkSame39 : original39 = target39 := by rfl

theorem chunkLength39 : (original39.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original40 from Data.GKRSetup.Unified.setupColumn5 start 5120 stop 5248
column_blocks_part target40Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 5120 stop 5248
noncomputable def target40 : List Setup.Block := target40Region6

theorem chunkSame40 : original40 = target40 := by rfl

theorem chunkLength40 : (original40.map Setup.Block.length).sum = 1080 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
