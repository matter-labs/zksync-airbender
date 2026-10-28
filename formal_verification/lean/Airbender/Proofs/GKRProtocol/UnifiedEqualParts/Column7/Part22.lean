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

column_blocks_part original89 from Data.GKRSetup.Unified.setupColumn7 start 11392 stop 11520
column_blocks_part target89Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 11392 stop 11520
noncomputable def target89 : List Setup.Block := target89Region6

theorem chunkSame89 : original89 = target89 := by rfl

theorem chunkLength89 : (original89.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original90 from Data.GKRSetup.Unified.setupColumn7 start 11520 stop 11648
column_blocks_part target90Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 11520 stop 11648
noncomputable def target90 : List Setup.Block := target90Region6

theorem chunkSame90 : original90 = target90 := by rfl

theorem chunkLength90 : (original90.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original91 from Data.GKRSetup.Unified.setupColumn7 start 11648 stop 11776
column_blocks_part target91Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 11648 stop 11776
noncomputable def target91 : List Setup.Block := target91Region6

theorem chunkSame91 : original91 = target91 := by rfl

theorem chunkLength91 : (original91.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original92 from Data.GKRSetup.Unified.setupColumn7 start 11776 stop 11904
column_blocks_part target92Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 11776 stop 11904
noncomputable def target92 : List Setup.Block := target92Region6

theorem chunkSame92 : original92 = target92 := by rfl

theorem chunkLength92 : (original92.map Setup.Block.length).sum = 1232 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
