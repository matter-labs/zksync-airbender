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

column_blocks_part original161 from Data.GKRSetup.Unified.setupColumn6 start 20608 stop 20736
column_blocks_part target161Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 20608 stop 20736
noncomputable def target161 : List Setup.Block := target161Region6

theorem chunkSame161 : original161 = target161 := by rfl

theorem chunkLength161 : (original161.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original162 from Data.GKRSetup.Unified.setupColumn6 start 20736 stop 20864
column_blocks_part target162Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 20736 stop 20864
noncomputable def target162 : List Setup.Block := target162Region6

theorem chunkSame162 : original162 = target162 := by rfl

theorem chunkLength162 : (original162.map Setup.Block.length).sum = 1210 := by decide +kernel

column_blocks_part original163 from Data.GKRSetup.Unified.setupColumn6 start 20864 stop 20992
column_blocks_part target163Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 20864 stop 20992
noncomputable def target163 : List Setup.Block := target163Region6

theorem chunkSame163 : original163 = target163 := by rfl

theorem chunkLength163 : (original163.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original164 from Data.GKRSetup.Unified.setupColumn6 start 20992 stop 21120
column_blocks_part target164Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 20992 stop 21120
noncomputable def target164 : List Setup.Block := target164Region6

theorem chunkSame164 : original164 = target164 := by rfl

theorem chunkLength164 : (original164.map Setup.Block.length).sum = 1214 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
