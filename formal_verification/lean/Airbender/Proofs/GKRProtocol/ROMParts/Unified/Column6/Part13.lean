import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front104 from Data.GKRSetup.Unified.setupColumn6 start 13312 stop 13440

theorem frontLength104 : (front104.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front105 from Data.GKRSetup.Unified.setupColumn6 start 13440 stop 13568

theorem frontLength105 : (front105.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front106 from Data.GKRSetup.Unified.setupColumn6 start 13568 stop 13696

theorem frontLength106 : (front106.map Setup.Block.length).sum = 2490 := by decide +kernel

column_blocks_part front107 from Data.GKRSetup.Unified.setupColumn6 start 13696 stop 13824

theorem frontLength107 : (front107.map Setup.Block.length).sum = 2296 := by decide +kernel

column_blocks_part front108 from Data.GKRSetup.Unified.setupColumn6 start 13824 stop 13952

theorem frontLength108 : (front108.map Setup.Block.length).sum = 2304 := by decide +kernel

column_blocks_part front109 from Data.GKRSetup.Unified.setupColumn6 start 13952 stop 14080

theorem frontLength109 : (front109.map Setup.Block.length).sum = 2094 := by decide +kernel

column_blocks_part front110 from Data.GKRSetup.Unified.setupColumn6 start 14080 stop 14208

theorem frontLength110 : (front110.map Setup.Block.length).sum = 2290 := by decide +kernel

column_blocks_part front111 from Data.GKRSetup.Unified.setupColumn6 start 14208 stop 14336

theorem frontLength111 : (front111.map Setup.Block.length).sum = 2304 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
