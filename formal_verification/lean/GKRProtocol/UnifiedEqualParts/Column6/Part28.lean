import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original113 from Data.GKRSetup.Unified.setupColumn6 start 14464 stop 14592
column_blocks_part target113Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 14464 stop 14592
noncomputable def target113 : List Setup.Block := target113Region6

theorem chunkSame113 : original113 = target113 := by rfl

theorem chunkLength113 : (original113.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part original114 from Data.GKRSetup.Unified.setupColumn6 start 14592 stop 14720
column_blocks_part target114Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 14592 stop 14720
noncomputable def target114 : List Setup.Block := target114Region6

theorem chunkSame114 : original114 = target114 := by rfl

theorem chunkLength114 : (original114.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part original115 from Data.GKRSetup.Unified.setupColumn6 start 14720 stop 14848
column_blocks_part target115Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 14720 stop 14848
noncomputable def target115 : List Setup.Block := target115Region6

theorem chunkSame115 : original115 = target115 := by rfl

theorem chunkLength115 : (original115.map Setup.Block.length).sum = 2078 := by decide +kernel

column_blocks_part original116 from Data.GKRSetup.Unified.setupColumn6 start 14848 stop 14976
column_blocks_part target116Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 14848 stop 14976
noncomputable def target116 : List Setup.Block := target116Region6

theorem chunkSame116 : original116 = target116 := by rfl

theorem chunkLength116 : (original116.map Setup.Block.length).sum = 2274 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
