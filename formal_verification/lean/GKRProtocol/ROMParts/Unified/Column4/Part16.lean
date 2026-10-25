import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front128 from Data.GKRSetup.Unified.setupColumn4 start 16384 stop 16512

theorem frontLength128 : (front128.map Setup.Block.length).sum = 1224 := by decide +kernel

column_blocks_part front129 from Data.GKRSetup.Unified.setupColumn4 start 16512 stop 16640

theorem frontLength129 : (front129.map Setup.Block.length).sum = 1088 := by decide +kernel

column_blocks_part front130 from Data.GKRSetup.Unified.setupColumn4 start 16640 stop 16768

theorem frontLength130 : (front130.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part front131 from Data.GKRSetup.Unified.setupColumn4 start 16768 stop 16896

theorem frontLength131 : (front131.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part front132 from Data.GKRSetup.Unified.setupColumn4 start 16896 stop 17024

theorem frontLength132 : (front132.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front133 from Data.GKRSetup.Unified.setupColumn4 start 17024 stop 17152

theorem frontLength133 : (front133.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front134 from Data.GKRSetup.Unified.setupColumn4 start 17152 stop 17280

theorem frontLength134 : (front134.map Setup.Block.length).sum = 1618 := by decide +kernel

column_blocks_part front135 from Data.GKRSetup.Unified.setupColumn4 start 17280 stop 17408

theorem frontLength135 : (front135.map Setup.Block.length).sum = 1694 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column4
