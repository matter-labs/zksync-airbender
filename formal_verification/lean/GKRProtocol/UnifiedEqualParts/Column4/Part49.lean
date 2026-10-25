import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original198 from Data.GKRSetup.Unified.setupColumn4 start 25344 stop 25472
column_blocks_part target198Region9 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 31 stop 159
noncomputable def target198 : List Setup.Block := target198Region9

theorem chunkSame198 : original198 = target198 := by rfl

theorem chunkLength198 : (original198.map Setup.Block.length).sum = 32768 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
