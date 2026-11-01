import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Data.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
-- This command group names the complete imported column data.
set_option maxHeartbeats 4000000

column_blocks_part original0 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 0 stop 128
column_blocks_part target0Region0 from (Verification.byteZeroData.columns[(2 : Nat)]) start 0 stop 1
column_blocks_part target0Region1 from (Verification.byteSignData.columns[(2 : Nat)]) start 0 stop 1
column_blocks_part target0Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 0 stop 128
noncomputable def target0 : List Setup.Block := target0Region0 ++ target0Region1 ++ target0Region2

column_blocks_part original1 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 128 stop 256
column_blocks_part target1Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 128 stop 256
noncomputable def target1 : List Setup.Block := target1Region2

column_blocks_part original2 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 256 stop 384
column_blocks_part target2Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 256 stop 384
noncomputable def target2 : List Setup.Block := target2Region2

column_blocks_part original3 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 384 stop 512
column_blocks_part target3Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 384 stop 512
noncomputable def target3 : List Setup.Block := target3Region2

column_blocks_part original4 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 512 stop 640
column_blocks_part target4Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 512 stop 640
noncomputable def target4 : List Setup.Block := target4Region2

column_blocks_part original5 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 640 stop 768
column_blocks_part target5Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 640 stop 768
noncomputable def target5 : List Setup.Block := target5Region2

column_blocks_part original6 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 768 stop 896
column_blocks_part target6Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 768 stop 896
noncomputable def target6 : List Setup.Block := target6Region2

column_blocks_part original7 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 896 stop 1024
column_blocks_part target7Region2 from (Verification.byteXorData.columns[(2 : Nat)]) start 896 stop 899
column_blocks_part target7Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 0 stop 125
noncomputable def target7 : List Setup.Block := target7Region2 ++ target7Region3

column_blocks_part original8 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1024 stop 1152
column_blocks_part target8Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 125 stop 253
noncomputable def target8 : List Setup.Block := target8Region3

column_blocks_part original9 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1152 stop 1280
column_blocks_part target9Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 253 stop 381
noncomputable def target9 : List Setup.Block := target9Region3

column_blocks_part original10 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1280 stop 1408
column_blocks_part target10Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 381 stop 509
noncomputable def target10 : List Setup.Block := target10Region3

column_blocks_part original11 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1408 stop 1536
column_blocks_part target11Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 509 stop 637
noncomputable def target11 : List Setup.Block := target11Region3

column_blocks_part original12 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1536 stop 1664
column_blocks_part target12Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 637 stop 765
noncomputable def target12 : List Setup.Block := target12Region3

column_blocks_part original13 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1664 stop 1792
column_blocks_part target13Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 765 stop 893
noncomputable def target13 : List Setup.Block := target13Region3

column_blocks_part original14 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1792 stop 1920
column_blocks_part target14Region3 from (Verification.byteOrData.columns[(2 : Nat)]) start 893 stop 898
column_blocks_part target14Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 0 stop 123
noncomputable def target14 : List Setup.Block := target14Region3 ++ target14Region4

column_blocks_part original15 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 1920 stop 2048
column_blocks_part target15Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 123 stop 251
noncomputable def target15 : List Setup.Block := target15Region4

column_blocks_part original16 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2048 stop 2176
column_blocks_part target16Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 251 stop 379
noncomputable def target16 : List Setup.Block := target16Region4

column_blocks_part original17 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2176 stop 2304
column_blocks_part target17Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 379 stop 507
noncomputable def target17 : List Setup.Block := target17Region4

column_blocks_part original18 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2304 stop 2432
column_blocks_part target18Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 507 stop 635
noncomputable def target18 : List Setup.Block := target18Region4

column_blocks_part original19 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2432 stop 2560
column_blocks_part target19Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 635 stop 763
noncomputable def target19 : List Setup.Block := target19Region4

column_blocks_part original20 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2560 stop 2688
column_blocks_part target20Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 763 stop 891
noncomputable def target20 : List Setup.Block := target20Region4

column_blocks_part original21 from Data.GKRSetup.ShiftBinop.setupColumn2
  start 2688 stop 2704
column_blocks_part target21Region4 from (Verification.byteAndData.columns[(2 : Nat)]) start 891 stop 898
column_blocks_part target21Region5 from (Verification.byteTruncateData.columns[(2 : Nat)]) start 0 stop 8
column_blocks_part target21Region6 from Verification.byteShiftColumn2 start 0 stop 1
noncomputable def target21 : List Setup.Block := target21Region4 ++ target21Region5 ++ target21Region6

end Airbender.Compiler.ShiftPrefixNative.Column2
