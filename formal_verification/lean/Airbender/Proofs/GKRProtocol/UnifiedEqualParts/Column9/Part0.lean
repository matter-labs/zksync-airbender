import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column9
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original0 from Data.GKRSetup.Unified.setupColumn9 start 0 stop 16
column_blocks_part target0Region0 from (UnifiedReduced.Setup.nativeZeroData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region2 from (UnifiedReduced.Setup.nativeCleanupData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region3 from (UnifiedReduced.Setup.nativeByteSignData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region4 from (UnifiedReduced.Setup.nativeSignData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region5 from (UnifiedReduced.Setup.nativeTruncationData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region7 from (UnifiedReduced.Setup.nativeROMData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region9 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region12 from (UnifiedReduced.Setup.nativeConditionalData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region13 from (UnifiedReduced.Setup.nativeXorData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region15 from (UnifiedReduced.Setup.nativeAndData.columns[(9 : Nat)]) start 0 stop 1
noncomputable def target0 : List Setup.Block := target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3 ++ target0Region4 ++ target0Region5 ++ target0Region6 ++ target0Region7 ++ target0Region8 ++ target0Region9 ++ target0Region10 ++ target0Region11 ++ target0Region12 ++ target0Region13 ++ target0Region14 ++ target0Region15

theorem chunkSame0 : original0 = target0 := by rfl

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 2097537 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column9
