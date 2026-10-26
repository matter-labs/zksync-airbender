import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front120 from Data.GKRSetup.Unified.setupColumn6 start 15360 stop 15488

theorem frontLength120 : (front120.map Setup.Block.length).sum = 2072 := by decide +kernel

column_blocks_part front121 from Data.GKRSetup.Unified.setupColumn6 start 15488 stop 15616

theorem frontLength121 : (front121.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front122 from Data.GKRSetup.Unified.setupColumn6 start 15616 stop 15744

theorem frontLength122 : (front122.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front123 from Data.GKRSetup.Unified.setupColumn6 start 15744 stop 15872

theorem frontLength123 : (front123.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front124 from Data.GKRSetup.Unified.setupColumn6 start 15872 stop 16000

theorem frontLength124 : (front124.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front125 from Data.GKRSetup.Unified.setupColumn6 start 16000 stop 16128

theorem frontLength125 : (front125.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front126 from Data.GKRSetup.Unified.setupColumn6 start 16128 stop 16256

theorem frontLength126 : (front126.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front127 from Data.GKRSetup.Unified.setupColumn6 start 16256 stop 16384

theorem frontLength127 : (front127.map Setup.Block.length).sum = 2048 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
