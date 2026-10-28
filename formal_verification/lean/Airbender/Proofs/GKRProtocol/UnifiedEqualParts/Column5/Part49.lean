import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original198 from Data.GKRSetup.Unified.setupColumn5 start 25344 stop 25472
column_blocks_part target198Region10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 784 stop 898
column_blocks_part target198Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 0 stop 14
noncomputable def target198 : List Setup.Block := target198Region10 ++ target198Region11

theorem chunkSame198 : original198 = target198 := by rfl

theorem chunkLength198 : (original198.map Setup.Block.length).sum = 21376 := by decide +kernel

column_blocks_part original199 from Data.GKRSetup.Unified.setupColumn5 start 25472 stop 25600
column_blocks_part target199Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 14 stop 142
noncomputable def target199 : List Setup.Block := target199Region11

theorem chunkSame199 : original199 = target199 := by rfl

theorem chunkLength199 : (original199.map Setup.Block.length).sum = 9220 := by decide +kernel

column_blocks_part original200 from Data.GKRSetup.Unified.setupColumn5 start 25600 stop 25728
column_blocks_part target200Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 142 stop 270
noncomputable def target200 : List Setup.Block := target200Region11

theorem chunkSame200 : original200 = target200 := by rfl

theorem chunkLength200 : (original200.map Setup.Block.length).sum = 6396 := by decide +kernel

column_blocks_part original201 from Data.GKRSetup.Unified.setupColumn5 start 25728 stop 25856
column_blocks_part target201Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 270 stop 398
noncomputable def target201 : List Setup.Block := target201Region11

theorem chunkSame201 : original201 = target201 := by rfl

theorem chunkLength201 : (original201.map Setup.Block.length).sum = 4888 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
