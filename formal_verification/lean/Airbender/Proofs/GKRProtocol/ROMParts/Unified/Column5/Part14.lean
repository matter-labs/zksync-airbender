import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front112 from Data.GKRSetup.Unified.setupColumn5 start 14336 stop 14464

theorem frontLength112 : (front112.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part front113 from Data.GKRSetup.Unified.setupColumn5 start 14464 stop 14592

theorem frontLength113 : (front113.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front114 from Data.GKRSetup.Unified.setupColumn5 start 14592 stop 14720

theorem frontLength114 : (front114.map Setup.Block.length).sum = 1184 := by decide +kernel

column_blocks_part front115 from Data.GKRSetup.Unified.setupColumn5 start 14720 stop 14848

theorem frontLength115 : (front115.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front116 from Data.GKRSetup.Unified.setupColumn5 start 14848 stop 14976

theorem frontLength116 : (front116.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part front117 from Data.GKRSetup.Unified.setupColumn5 start 14976 stop 15104

theorem frontLength117 : (front117.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front118 from Data.GKRSetup.Unified.setupColumn5 start 15104 stop 15232

theorem frontLength118 : (front118.map Setup.Block.length).sum = 1200 := by decide +kernel

column_blocks_part front119 from Data.GKRSetup.Unified.setupColumn5 start 15232 stop 15360

theorem frontLength119 : (front119.map Setup.Block.length).sum = 1064 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column5
