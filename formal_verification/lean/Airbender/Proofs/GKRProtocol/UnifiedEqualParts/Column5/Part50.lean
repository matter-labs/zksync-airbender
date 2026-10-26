import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original202 from Data.GKRSetup.Unified.setupColumn5 start 25856 stop 25984
column_blocks_part target202Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 398 stop 526
noncomputable def target202 : List Setup.Block := target202Region11

theorem chunkSame202 : original202 = target202 := by rfl

theorem chunkLength202 : (original202.map Setup.Block.length).sum = 11752 := by decide +kernel

column_blocks_part original203 from Data.GKRSetup.Unified.setupColumn5 start 25984 stop 26112
column_blocks_part target203Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 526 stop 654
noncomputable def target203 : List Setup.Block := target203Region11

theorem chunkSame203 : original203 = target203 := by rfl

theorem chunkLength203 : (original203.map Setup.Block.length).sum = 9472 := by decide +kernel

column_blocks_part original204 from Data.GKRSetup.Unified.setupColumn5 start 26112 stop 26240
column_blocks_part target204Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 654 stop 782
noncomputable def target204 : List Setup.Block := target204Region11

theorem chunkSame204 : original204 = target204 := by rfl

theorem chunkLength204 : (original204.map Setup.Block.length).sum = 6336 := by decide +kernel

column_blocks_part original205 from Data.GKRSetup.Unified.setupColumn5 start 26240 stop 26368
column_blocks_part target205Region11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 782 stop 910
noncomputable def target205 : List Setup.Block := target205Region11

theorem chunkSame205 : original205 = target205 := by rfl

theorem chunkLength205 : (original205.map Setup.Block.length).sum = 5176 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
