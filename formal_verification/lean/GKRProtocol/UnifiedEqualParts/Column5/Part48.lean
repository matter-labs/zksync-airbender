import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original194 from Data.GKRSetup.Unified.setupColumn5 start 24832 stop 24960
column_blocks_part target194Region10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 272 stop 400
noncomputable def target194 : List Setup.Block := target194Region10

theorem chunkSame194 : original194 = target194 := by rfl

theorem chunkLength194 : (original194.map Setup.Block.length).sum = 4360 := by decide +kernel

column_blocks_part original195 from Data.GKRSetup.Unified.setupColumn5 start 24960 stop 25088
column_blocks_part target195Region10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 400 stop 528
noncomputable def target195 : List Setup.Block := target195Region10

theorem chunkSame195 : original195 = target195 := by rfl

theorem chunkLength195 : (original195.map Setup.Block.length).sum = 14944 := by decide +kernel

column_blocks_part original196 from Data.GKRSetup.Unified.setupColumn5 start 25088 stop 25216
column_blocks_part target196Region10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 528 stop 656
noncomputable def target196 : List Setup.Block := target196Region10

theorem chunkSame196 : original196 = target196 := by rfl

theorem chunkLength196 : (original196.map Setup.Block.length).sum = 2392 := by decide +kernel

column_blocks_part original197 from Data.GKRSetup.Unified.setupColumn5 start 25216 stop 25344
column_blocks_part target197Region10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 656 stop 784
noncomputable def target197 : List Setup.Block := target197Region10

theorem chunkSame197 : original197 = target197 := by rfl

theorem chunkLength197 : (original197.map Setup.Block.length).sum = 2120 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
