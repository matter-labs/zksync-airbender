import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original109 from Data.GKRSetup.Unified.setupColumn6 start 13952 stop 14080
column_blocks_part target109Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 13952 stop 14080
noncomputable def target109 : List Setup.Block := target109Region6

theorem chunkSame109 : original109 = target109 := by rfl

theorem chunkLength109 : (original109.map Setup.Block.length).sum = 2094 := by decide +kernel

column_blocks_part original110 from Data.GKRSetup.Unified.setupColumn6 start 14080 stop 14208
column_blocks_part target110Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 14080 stop 14208
noncomputable def target110 : List Setup.Block := target110Region6

theorem chunkSame110 : original110 = target110 := by rfl

theorem chunkLength110 : (original110.map Setup.Block.length).sum = 2290 := by decide +kernel

column_blocks_part original111 from Data.GKRSetup.Unified.setupColumn6 start 14208 stop 14336
column_blocks_part target111Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 14208 stop 14336
noncomputable def target111 : List Setup.Block := target111Region6

theorem chunkSame111 : original111 = target111 := by rfl

theorem chunkLength111 : (original111.map Setup.Block.length).sum = 2304 := by decide +kernel

column_blocks_part original112 from Data.GKRSetup.Unified.setupColumn6 start 14336 stop 14464
column_blocks_part target112Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 14336 stop 14464
noncomputable def target112 : List Setup.Block := target112Region6

theorem chunkSame112 : original112 = target112 := by rfl

theorem chunkLength112 : (original112.map Setup.Block.length).sum = 2288 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
