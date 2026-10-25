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

column_blocks_part original169 from Data.GKRSetup.Unified.setupColumn7 start 21632 stop 21760
column_blocks_part target169Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 21632 stop 21760
noncomputable def target169 : List Setup.Block := target169Region6

theorem chunkSame169 : original169 = target169 := by rfl

theorem chunkLength169 : (original169.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original170 from Data.GKRSetup.Unified.setupColumn7 start 21760 stop 21888
column_blocks_part target170Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 21760 stop 21888
noncomputable def target170 : List Setup.Block := target170Region6

theorem chunkSame170 : original170 = target170 := by rfl

theorem chunkLength170 : (original170.map Setup.Block.length).sum = 2272 := by decide +kernel

column_blocks_part original171 from Data.GKRSetup.Unified.setupColumn7 start 21888 stop 22016
column_blocks_part target171Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 21888 stop 22016
noncomputable def target171 : List Setup.Block := target171Region6

theorem chunkSame171 : original171 = target171 := by rfl

theorem chunkLength171 : (original171.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original172 from Data.GKRSetup.Unified.setupColumn7 start 22016 stop 22144
column_blocks_part target172Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 22016 stop 22144
noncomputable def target172 : List Setup.Block := target172Region6

theorem chunkSame172 : original172 = target172 := by rfl

theorem chunkLength172 : (original172.map Setup.Block.length).sum = 2280 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
