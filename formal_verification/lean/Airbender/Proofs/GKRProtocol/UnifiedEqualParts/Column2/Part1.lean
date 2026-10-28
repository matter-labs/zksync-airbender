import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original5 from Data.GKRSetup.Unified.setupColumn2 start 640 stop 768
column_blocks_part target5Region13 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 623 stop 751
noncomputable def target5 : List Setup.Block := target5Region13

theorem chunkSame5 : original5 = target5 := by rfl

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 1368 := by decide +kernel

column_blocks_part original6 from Data.GKRSetup.Unified.setupColumn2 start 768 stop 896
column_blocks_part target6Region13 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 751 stop 879
noncomputable def target6 : List Setup.Block := target6Region13

theorem chunkSame6 : original6 = target6 := by rfl

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 15680 := by decide +kernel

column_blocks_part original7 from Data.GKRSetup.Unified.setupColumn2 start 896 stop 1024
column_blocks_part target7Region13 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 879 stop 899
column_blocks_part target7Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 0 stop 108
noncomputable def target7 : List Setup.Block := target7Region13 ++ target7Region14

theorem chunkSame7 : original7 = target7 := by rfl

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 24320 := by decide +kernel

column_blocks_part original8 from Data.GKRSetup.Unified.setupColumn2 start 1024 stop 1152
column_blocks_part target8Region14 from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 108 stop 236
noncomputable def target8 : List Setup.Block := target8Region14

theorem chunkSame8 : original8 = target8 := by rfl

theorem chunkLength8 : (original8.map Setup.Block.length).sum = 2480 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column2
