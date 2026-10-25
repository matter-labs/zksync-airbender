import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front160 from Data.GKRSetup.Unified.setupColumn6 start 20480 stop 20608

theorem frontLength160 : (front160.map Setup.Block.length).sum = 1286 := by decide +kernel

column_blocks_part front161 from Data.GKRSetup.Unified.setupColumn6 start 20608 stop 20736

theorem frontLength161 : (front161.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part front162 from Data.GKRSetup.Unified.setupColumn6 start 20736 stop 20864

theorem frontLength162 : (front162.map Setup.Block.length).sum = 1210 := by decide +kernel

column_blocks_part front163 from Data.GKRSetup.Unified.setupColumn6 start 20864 stop 20992

theorem frontLength163 : (front163.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part front164 from Data.GKRSetup.Unified.setupColumn6 start 20992 stop 21120

theorem frontLength164 : (front164.map Setup.Block.length).sum = 1214 := by decide +kernel

column_blocks_part front165 from Data.GKRSetup.Unified.setupColumn6 start 21120 stop 21248

theorem frontLength165 : (front165.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part front166 from Data.GKRSetup.Unified.setupColumn6 start 21248 stop 21376

theorem frontLength166 : (front166.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part front167 from Data.GKRSetup.Unified.setupColumn6 start 21376 stop 21504

theorem frontLength167 : (front167.map Setup.Block.length).sum = 1234 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
