import Airbender.Proofs.GKRProtocol.BlockSpans
import Airbender.Import.GKRProtocol.BlockCoverageImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original from Data.GKRSetup.Unified.setupColumn5 start 0 stop 128

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
