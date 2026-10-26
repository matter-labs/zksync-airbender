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

column_blocks_part original185 from Data.GKRSetup.Unified.setupColumn6 start 23680 stop 23808
column_blocks_part target185Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 23680 stop 23808
noncomputable def target185 : List Setup.Block := target185Region6

theorem chunkSame185 : original185 = target185 := by rfl

theorem chunkLength185 : (original185.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part original186 from Data.GKRSetup.Unified.setupColumn6 start 23808 stop 23936
column_blocks_part target186Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 23808 stop 23936
noncomputable def target186 : List Setup.Block := target186Region6

theorem chunkSame186 : original186 = target186 := by rfl

theorem chunkLength186 : (original186.map Setup.Block.length).sum = 1226 := by decide +kernel

column_blocks_part original187 from Data.GKRSetup.Unified.setupColumn6 start 23936 stop 24064
column_blocks_part target187Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 23936 stop 24064
noncomputable def target187 : List Setup.Block := target187Region6

theorem chunkSame187 : original187 = target187 := by rfl

theorem chunkLength187 : (original187.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part original188 from Data.GKRSetup.Unified.setupColumn6 start 24064 stop 24192
column_blocks_part target188Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24064 stop 24192
noncomputable def target188 : List Setup.Block := target188Region6

theorem chunkSame188 : original188 = target188 := by rfl

theorem chunkLength188 : (original188.map Setup.Block.length).sum = 1064 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
