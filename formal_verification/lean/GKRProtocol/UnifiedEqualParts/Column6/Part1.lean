import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original5 from Data.GKRSetup.Unified.setupColumn6 start 640 stop 768
column_blocks_part target5Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 640 stop 768
noncomputable def target5 : List Setup.Block := target5Region6

theorem chunkSame5 : original5 = target5 := by rfl

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 1488 := by decide +kernel

column_blocks_part original6 from Data.GKRSetup.Unified.setupColumn6 start 768 stop 896
column_blocks_part target6Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 768 stop 896
noncomputable def target6 : List Setup.Block := target6Region6

theorem chunkSame6 : original6 = target6 := by rfl

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 1304 := by decide +kernel

column_blocks_part original7 from Data.GKRSetup.Unified.setupColumn6 start 896 stop 1024
column_blocks_part target7Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 896 stop 1024
noncomputable def target7 : List Setup.Block := target7Region6

theorem chunkSame7 : original7 = target7 := by rfl

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 1304 := by decide +kernel

column_blocks_part original8 from Data.GKRSetup.Unified.setupColumn6 start 1024 stop 1152
column_blocks_part target8Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 1024 stop 1152
noncomputable def target8 : List Setup.Block := target8Region6

theorem chunkSame8 : original8 = target8 := by rfl

theorem chunkLength8 : (original8.map Setup.Block.length).sum = 1480 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
