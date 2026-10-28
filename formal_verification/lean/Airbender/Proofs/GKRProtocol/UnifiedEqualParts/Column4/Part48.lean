import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original194 from Data.GKRSetup.Unified.setupColumn4 start 24832 stop 24960
column_blocks_part target194Region8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 418 stop 546
noncomputable def target194 : List Setup.Block := target194Region8

theorem chunkSame194 : original194 = target194 := by rfl

theorem chunkLength194 : (original194.map Setup.Block.length).sum = 13312 := by decide +kernel

column_blocks_part original195 from Data.GKRSetup.Unified.setupColumn4 start 24960 stop 25088
column_blocks_part target195Region8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 546 stop 674
noncomputable def target195 : List Setup.Block := target195Region8

theorem chunkSame195 : original195 = target195 := by rfl

theorem chunkLength195 : (original195.map Setup.Block.length).sum = 1916 := by decide +kernel

column_blocks_part original196 from Data.GKRSetup.Unified.setupColumn4 start 25088 stop 25216
column_blocks_part target196Region8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 674 stop 802
noncomputable def target196 : List Setup.Block := target196Region8

theorem chunkSame196 : original196 = target196 := by rfl

theorem chunkLength196 : (original196.map Setup.Block.length).sum = 3140 := by decide +kernel

column_blocks_part original197 from Data.GKRSetup.Unified.setupColumn4 start 25216 stop 25344
column_blocks_part target197Region8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 802 stop 899
column_blocks_part target197Region9 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 0 stop 31
noncomputable def target197 : List Setup.Block := target197Region8 ++ target197Region9

theorem chunkSame197 : original197 = target197 := by rfl

theorem chunkLength197 : (original197.map Setup.Block.length).sum = 26432 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
