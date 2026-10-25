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

column_blocks_part original189 from Data.GKRSetup.Unified.setupColumn7 start 24192 stop 24320
column_blocks_part target189Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24192 stop 24320
noncomputable def target189 : List Setup.Block := target189Region6

theorem chunkSame189 : original189 = target189 := by rfl

theorem chunkLength189 : (original189.map Setup.Block.length).sum = 1800 := by decide +kernel

column_blocks_part original190 from Data.GKRSetup.Unified.setupColumn7 start 24320 stop 24448
column_blocks_part target190Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24320 stop 24448
noncomputable def target190 : List Setup.Block := target190Region6

theorem chunkSame190 : original190 = target190 := by rfl

theorem chunkLength190 : (original190.map Setup.Block.length).sum = 1800 := by decide +kernel

column_blocks_part original191 from Data.GKRSetup.Unified.setupColumn7 start 24448 stop 24576
column_blocks_part target191Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24448 stop 24576
noncomputable def target191 : List Setup.Block := target191Region6

theorem chunkSame191 : original191 = target191 := by rfl

theorem chunkLength191 : (original191.map Setup.Block.length).sum = 1800 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
