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

column_blocks_part original105 from Data.GKRSetup.Unified.setupColumn5 start 13440 stop 13568
column_blocks_part target105Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 13440 stop 13568
noncomputable def target105 : List Setup.Block := target105Region6

theorem chunkSame105 : original105 = target105 := by rfl

theorem chunkLength105 : (original105.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part original106 from Data.GKRSetup.Unified.setupColumn5 start 13568 stop 13696
column_blocks_part target106Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 13568 stop 13696
noncomputable def target106 : List Setup.Block := target106Region6

theorem chunkSame106 : original106 = target106 := by rfl

theorem chunkLength106 : (original106.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original107 from Data.GKRSetup.Unified.setupColumn5 start 13696 stop 13824
column_blocks_part target107Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 13696 stop 13824
noncomputable def target107 : List Setup.Block := target107Region6

theorem chunkSame107 : original107 = target107 := by rfl

theorem chunkLength107 : (original107.map Setup.Block.length).sum = 1218 := by decide +kernel

column_blocks_part original108 from Data.GKRSetup.Unified.setupColumn5 start 13824 stop 13952
column_blocks_part target108Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 13824 stop 13952
noncomputable def target108 : List Setup.Block := target108Region6

theorem chunkSame108 : original108 = target108 := by rfl

theorem chunkLength108 : (original108.map Setup.Block.length).sum = 1110 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
