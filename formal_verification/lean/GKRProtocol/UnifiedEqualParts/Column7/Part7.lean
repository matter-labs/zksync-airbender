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

column_blocks_part original29 from Data.GKRSetup.Unified.setupColumn7 start 3712 stop 3840
column_blocks_part target29Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 3712 stop 3840
noncomputable def target29 : List Setup.Block := target29Region6

theorem chunkSame29 : original29 = target29 := by rfl

theorem chunkLength29 : (original29.map Setup.Block.length).sum = 1208 := by decide +kernel

column_blocks_part original30 from Data.GKRSetup.Unified.setupColumn7 start 3840 stop 3968
column_blocks_part target30Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 3840 stop 3968
noncomputable def target30 : List Setup.Block := target30Region6

theorem chunkSame30 : original30 = target30 := by rfl

theorem chunkLength30 : (original30.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part original31 from Data.GKRSetup.Unified.setupColumn7 start 3968 stop 4096
column_blocks_part target31Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 3968 stop 4096
noncomputable def target31 : List Setup.Block := target31Region6

theorem chunkSame31 : original31 = target31 := by rfl

theorem chunkLength31 : (original31.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part original32 from Data.GKRSetup.Unified.setupColumn7 start 4096 stop 4224
column_blocks_part target32Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 4096 stop 4224
noncomputable def target32 : List Setup.Block := target32Region6

theorem chunkSame32 : original32 = target32 := by rfl

theorem chunkLength32 : (original32.map Setup.Block.length).sum = 1048 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
