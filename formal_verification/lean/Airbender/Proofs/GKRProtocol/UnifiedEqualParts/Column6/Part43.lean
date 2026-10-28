import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original173 from Data.GKRSetup.Unified.setupColumn6 start 22144 stop 22272
column_blocks_part target173Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 22144 stop 22272
noncomputable def target173 : List Setup.Block := target173Region6

theorem chunkSame173 : original173 = target173 := by rfl

theorem chunkLength173 : (original173.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part original174 from Data.GKRSetup.Unified.setupColumn6 start 22272 stop 22400
column_blocks_part target174Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 22272 stop 22400
noncomputable def target174 : List Setup.Block := target174Region6

theorem chunkSame174 : original174 = target174 := by rfl

theorem chunkLength174 : (original174.map Setup.Block.length).sum = 1198 := by decide +kernel

column_blocks_part original175 from Data.GKRSetup.Unified.setupColumn6 start 22400 stop 22528
column_blocks_part target175Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 22400 stop 22528
noncomputable def target175 : List Setup.Block := target175Region6

theorem chunkSame175 : original175 = target175 := by rfl

theorem chunkLength175 : (original175.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part original176 from Data.GKRSetup.Unified.setupColumn6 start 22528 stop 22656
column_blocks_part target176Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 22528 stop 22656
noncomputable def target176 : List Setup.Block := target176Region6

theorem chunkSame176 : original176 = target176 := by rfl

theorem chunkLength176 : (original176.map Setup.Block.length).sum = 1193 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
