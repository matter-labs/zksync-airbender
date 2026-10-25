import GKRProtocol.BlockSpans
import GKRProtocol.BlockCoverageImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original from Data.GKRSetup.Unified.setupColumn1 start 0 stop 34
column_blocks_part suffix from Data.GKRSetup.Unified.setupColumn1 start 34 stop 37

end Airbender.Compiler.UnifiedPrefixNative.Column1
