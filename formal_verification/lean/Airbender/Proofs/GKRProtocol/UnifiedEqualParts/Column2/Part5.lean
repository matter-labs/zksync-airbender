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

column_blocks_part original21 from Data.GKRSetup.Unified.setupColumn2 start 2688 stop 2712
column_blocks_part target21Region15 from (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]) start 874 stop 898
noncomputable def target21 : List Setup.Block := target21Region15

theorem chunkSame21 : original21 = target21 := by rfl

theorem chunkLength21 : (original21.map Setup.Block.length).sum = 6144 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column2
