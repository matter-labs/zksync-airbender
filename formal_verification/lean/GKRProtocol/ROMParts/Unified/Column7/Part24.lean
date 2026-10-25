import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front192 from Data.GKRSetup.Unified.setupColumn7 start 24576 stop 24668

theorem frontLength192 : (front192.map Setup.Block.length).sum = 1287 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column7
