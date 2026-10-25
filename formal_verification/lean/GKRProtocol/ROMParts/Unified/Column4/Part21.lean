import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front168 from Data.GKRSetup.Unified.setupColumn4 start 21504 stop 21632

theorem frontLength168 : (front168.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part front169 from Data.GKRSetup.Unified.setupColumn4 start 21632 stop 21760

theorem frontLength169 : (front169.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front170 from Data.GKRSetup.Unified.setupColumn4 start 21760 stop 21888

theorem frontLength170 : (front170.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part front171 from Data.GKRSetup.Unified.setupColumn4 start 21888 stop 22016

theorem frontLength171 : (front171.map Setup.Block.length).sum = 1208 := by decide +kernel

column_blocks_part front172 from Data.GKRSetup.Unified.setupColumn4 start 22016 stop 22144

theorem frontLength172 : (front172.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front173 from Data.GKRSetup.Unified.setupColumn4 start 22144 stop 22272

theorem frontLength173 : (front173.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part front174 from Data.GKRSetup.Unified.setupColumn4 start 22272 stop 22400

theorem frontLength174 : (front174.map Setup.Block.length).sum = 1050 := by decide +kernel

column_blocks_part front175 from Data.GKRSetup.Unified.setupColumn4 start 22400 stop 22528

theorem frontLength175 : (front175.map Setup.Block.length).sum = 1206 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column4
