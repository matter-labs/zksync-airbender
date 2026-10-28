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

column_blocks_part original53 from Data.GKRSetup.Unified.setupColumn5 start 6784 stop 6912
column_blocks_part target53Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 6784 stop 6912
noncomputable def target53 : List Setup.Block := target53Region6

theorem chunkSame53 : original53 = target53 := by rfl

theorem chunkLength53 : (original53.map Setup.Block.length).sum = 2296 := by decide +kernel

column_blocks_part original54 from Data.GKRSetup.Unified.setupColumn5 start 6912 stop 7040
column_blocks_part target54Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 6912 stop 7040
noncomputable def target54 : List Setup.Block := target54Region6

theorem chunkSame54 : original54 = target54 := by rfl

theorem chunkLength54 : (original54.map Setup.Block.length).sum = 2304 := by decide +kernel

column_blocks_part original55 from Data.GKRSetup.Unified.setupColumn5 start 7040 stop 7168
column_blocks_part target55Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 7040 stop 7168
noncomputable def target55 : List Setup.Block := target55Region6

theorem chunkSame55 : original55 = target55 := by rfl

theorem chunkLength55 : (original55.map Setup.Block.length).sum = 2288 := by decide +kernel

column_blocks_part original56 from Data.GKRSetup.Unified.setupColumn5 start 7168 stop 7296
column_blocks_part target56Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 7168 stop 7296
noncomputable def target56 : List Setup.Block := target56Region6

theorem chunkSame56 : original56 = target56 := by rfl

theorem chunkLength56 : (original56.map Setup.Block.length).sum = 2304 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
