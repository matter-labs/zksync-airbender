import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original181 from Data.GKRSetup.Unified.setupColumn7 start 23168 stop 23296
column_blocks_part target181Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 23168 stop 23296
noncomputable def target181 : List Setup.Block := target181Region6

theorem chunkSame181 : original181 = target181 := by rfl

theorem chunkLength181 : (original181.map Setup.Block.length).sum = 1800 := by decide +kernel

column_blocks_part original182 from Data.GKRSetup.Unified.setupColumn7 start 23296 stop 23424
column_blocks_part target182Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 23296 stop 23424
noncomputable def target182 : List Setup.Block := target182Region6

theorem chunkSame182 : original182 = target182 := by rfl

theorem chunkLength182 : (original182.map Setup.Block.length).sum = 1800 := by decide +kernel

column_blocks_part original183 from Data.GKRSetup.Unified.setupColumn7 start 23424 stop 23552
column_blocks_part target183Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 23424 stop 23552
noncomputable def target183 : List Setup.Block := target183Region6

theorem chunkSame183 : original183 = target183 := by rfl

theorem chunkLength183 : (original183.map Setup.Block.length).sum = 1799 := by decide +kernel

column_blocks_part original184 from Data.GKRSetup.Unified.setupColumn7 start 23552 stop 23680
column_blocks_part target184Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 23552 stop 23680
noncomputable def target184 : List Setup.Block := target184Region6

theorem chunkSame184 : original184 = target184 := by rfl

theorem chunkLength184 : (original184.map Setup.Block.length).sum = 1985 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
