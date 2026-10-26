import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original121 from Data.GKRSetup.Unified.setupColumn5 start 15488 stop 15616
column_blocks_part target121Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 15488 stop 15616
noncomputable def target121 : List Setup.Block := target121Region6

theorem chunkSame121 : original121 = target121 := by rfl

theorem chunkLength121 : (original121.map Setup.Block.length).sum = 1186 := by decide +kernel

column_blocks_part original122 from Data.GKRSetup.Unified.setupColumn5 start 15616 stop 15744
column_blocks_part target122Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 15616 stop 15744
noncomputable def target122 : List Setup.Block := target122Region6

theorem chunkSame122 : original122 = target122 := by rfl

theorem chunkLength122 : (original122.map Setup.Block.length).sum = 1046 := by decide +kernel

column_blocks_part original123 from Data.GKRSetup.Unified.setupColumn5 start 15744 stop 15872
column_blocks_part target123Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 15744 stop 15872
noncomputable def target123 : List Setup.Block := target123Region6

theorem chunkSame123 : original123 = target123 := by rfl

theorem chunkLength123 : (original123.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original124 from Data.GKRSetup.Unified.setupColumn5 start 15872 stop 16000
column_blocks_part target124Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 15872 stop 16000
noncomputable def target124 : List Setup.Block := target124Region6

theorem chunkSame124 : original124 = target124 := by rfl

theorem chunkLength124 : (original124.map Setup.Block.length).sum = 1048 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
