import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front80 from Data.GKRSetup.Unified.setupColumn4 start 10240 stop 10368

theorem frontLength80 : (front80.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front81 from Data.GKRSetup.Unified.setupColumn4 start 10368 stop 10496

theorem frontLength81 : (front81.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part front82 from Data.GKRSetup.Unified.setupColumn4 start 10496 stop 10624

theorem frontLength82 : (front82.map Setup.Block.length).sum = 1632 := by decide +kernel

column_blocks_part front83 from Data.GKRSetup.Unified.setupColumn4 start 10624 stop 10752

theorem frontLength83 : (front83.map Setup.Block.length).sum = 1792 := by decide +kernel

column_blocks_part front84 from Data.GKRSetup.Unified.setupColumn4 start 10752 stop 10880

theorem frontLength84 : (front84.map Setup.Block.length).sum = 1576 := by decide +kernel

column_blocks_part front85 from Data.GKRSetup.Unified.setupColumn4 start 10880 stop 11008

theorem frontLength85 : (front85.map Setup.Block.length).sum = 1504 := by decide +kernel

column_blocks_part front86 from Data.GKRSetup.Unified.setupColumn4 start 11008 stop 11136

theorem frontLength86 : (front86.map Setup.Block.length).sum = 1520 := by decide +kernel

column_blocks_part front87 from Data.GKRSetup.Unified.setupColumn4 start 11136 stop 11264

theorem frontLength87 : (front87.map Setup.Block.length).sum = 1512 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column4
