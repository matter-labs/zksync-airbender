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

column_blocks_part original85 from Data.GKRSetup.Unified.setupColumn5 start 10880 stop 11008
column_blocks_part target85Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 10880 stop 11008
noncomputable def target85 : List Setup.Block := target85Region6

theorem chunkSame85 : original85 = target85 := by rfl

theorem chunkLength85 : (original85.map Setup.Block.length).sum = 1336 := by decide +kernel

column_blocks_part original86 from Data.GKRSetup.Unified.setupColumn5 start 11008 stop 11136
column_blocks_part target86Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 11008 stop 11136
noncomputable def target86 : List Setup.Block := target86Region6

theorem chunkSame86 : original86 = target86 := by rfl

theorem chunkLength86 : (original86.map Setup.Block.length).sum = 1458 := by decide +kernel

column_blocks_part original87 from Data.GKRSetup.Unified.setupColumn5 start 11136 stop 11264
column_blocks_part target87Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 11136 stop 11264
noncomputable def target87 : List Setup.Block := target87Region6

theorem chunkSame87 : original87 = target87 := by rfl

theorem chunkLength87 : (original87.map Setup.Block.length).sum = 1302 := by decide +kernel

column_blocks_part original88 from Data.GKRSetup.Unified.setupColumn5 start 11264 stop 11392
column_blocks_part target88Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 11264 stop 11392
noncomputable def target88 : List Setup.Block := target88Region6

theorem chunkSame88 : original88 = target88 := by rfl

theorem chunkLength88 : (original88.map Setup.Block.length).sum = 1304 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
