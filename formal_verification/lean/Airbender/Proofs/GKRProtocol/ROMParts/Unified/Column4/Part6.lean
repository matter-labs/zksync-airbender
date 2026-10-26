import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front48 from Data.GKRSetup.Unified.setupColumn4 start 6144 stop 6272

theorem frontLength48 : (front48.map Setup.Block.length).sum = 1296 := by decide +kernel

column_blocks_part front49 from Data.GKRSetup.Unified.setupColumn4 start 6272 stop 6400

theorem frontLength49 : (front49.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part front50 from Data.GKRSetup.Unified.setupColumn4 start 6400 stop 6528

theorem frontLength50 : (front50.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part front51 from Data.GKRSetup.Unified.setupColumn4 start 6528 stop 6656

theorem frontLength51 : (front51.map Setup.Block.length).sum = 1272 := by decide +kernel

column_blocks_part front52 from Data.GKRSetup.Unified.setupColumn4 start 6656 stop 6784

theorem frontLength52 : (front52.map Setup.Block.length).sum = 1112 := by decide +kernel

column_blocks_part front53 from Data.GKRSetup.Unified.setupColumn4 start 6784 stop 6912

theorem frontLength53 : (front53.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part front54 from Data.GKRSetup.Unified.setupColumn4 start 6912 stop 7040

theorem frontLength54 : (front54.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part front55 from Data.GKRSetup.Unified.setupColumn4 start 7040 stop 7168

theorem frontLength55 : (front55.map Setup.Block.length).sum = 1224 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column4
