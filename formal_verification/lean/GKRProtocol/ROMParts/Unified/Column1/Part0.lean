import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front0 from Data.GKRSetup.Unified.setupColumn1 start 0 stop 12

theorem frontLength0 : (front0.map Setup.Block.length).sum = 590081 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column1
