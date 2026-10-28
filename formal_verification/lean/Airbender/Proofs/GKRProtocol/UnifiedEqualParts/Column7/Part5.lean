import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original21 from Data.GKRSetup.Unified.setupColumn7 start 2688 stop 2816
column_blocks_part target21Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 2688 stop 2816
noncomputable def target21 : List Setup.Block := target21Region6

theorem chunkSame21 : original21 = target21 := by rfl

theorem chunkLength21 : (original21.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original22 from Data.GKRSetup.Unified.setupColumn7 start 2816 stop 2944
column_blocks_part target22Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 2816 stop 2944
noncomputable def target22 : List Setup.Block := target22Region6

theorem chunkSame22 : original22 = target22 := by rfl

theorem chunkLength22 : (original22.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original23 from Data.GKRSetup.Unified.setupColumn7 start 2944 stop 3072
column_blocks_part target23Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 2944 stop 3072
noncomputable def target23 : List Setup.Block := target23Region6

theorem chunkSame23 : original23 = target23 := by rfl

theorem chunkLength23 : (original23.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original24 from Data.GKRSetup.Unified.setupColumn7 start 3072 stop 3200
column_blocks_part target24Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 3072 stop 3200
noncomputable def target24 : List Setup.Block := target24Region6

theorem chunkSame24 : original24 = target24 := by rfl

theorem chunkLength24 : (original24.map Setup.Block.length).sum = 1232 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
