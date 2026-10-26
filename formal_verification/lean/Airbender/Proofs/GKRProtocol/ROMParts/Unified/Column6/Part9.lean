import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front72 from Data.GKRSetup.Unified.setupColumn6 start 9216 stop 9344

theorem frontLength72 : (front72.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front73 from Data.GKRSetup.Unified.setupColumn6 start 9344 stop 9472

theorem frontLength73 : (front73.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front74 from Data.GKRSetup.Unified.setupColumn6 start 9472 stop 9600

theorem frontLength74 : (front74.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front75 from Data.GKRSetup.Unified.setupColumn6 start 9600 stop 9728

theorem frontLength75 : (front75.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front76 from Data.GKRSetup.Unified.setupColumn6 start 9728 stop 9856

theorem frontLength76 : (front76.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front77 from Data.GKRSetup.Unified.setupColumn6 start 9856 stop 9984

theorem frontLength77 : (front77.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front78 from Data.GKRSetup.Unified.setupColumn6 start 9984 stop 10112

theorem frontLength78 : (front78.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part front79 from Data.GKRSetup.Unified.setupColumn6 start 10112 stop 10240

theorem frontLength79 : (front79.map Setup.Block.length).sum = 1240 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
