import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

noncomputable def source14 : Setup.Block := original.get ⟨14, by decide +kernel⟩

column_blocks_part part14_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination14_0 : Setup.Block := part14_0.get ⟨0, by decide +kernel⟩

column_blocks_part part14_1 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination14_1 : Setup.Block := part14_1.get ⟨0, by decide +kernel⟩

column_blocks_part part14_2 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination14_2 : Setup.Block := part14_2.get ⟨0, by decide +kernel⟩

column_blocks_part part14_3 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination14_3 : Setup.Block := part14_3.get ⟨0, by decide +kernel⟩

column_blocks_part part14_4 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination14_4 : Setup.Block := part14_4.get ⟨0, by decide +kernel⟩

column_blocks_part part14_5 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination14_5 : Setup.Block := part14_5.get ⟨0, by decide +kernel⟩

column_blocks_part part14_6 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination14_6 : Setup.Block := part14_6.get ⟨0, by decide +kernel⟩

column_blocks_part part14_7 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination14_7 : Setup.Block := part14_7.get ⟨0, by decide +kernel⟩

column_blocks_part part14_8 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination14_8 : Setup.Block := part14_8.get ⟨0, by decide +kernel⟩

column_blocks_part part14_9 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination14_9 : Setup.Block := part14_9.get ⟨0, by decide +kernel⟩

column_blocks_part part14_10 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination14_10 : Setup.Block := part14_10.get ⟨0, by decide +kernel⟩

column_blocks_part part14_11 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination14_11 : Setup.Block := part14_11.get ⟨0, by decide +kernel⟩

noncomputable def target14 : List Setup.Block := part14_0 ++ part14_1 ++ part14_2 ++ part14_3 ++ part14_4 ++ part14_5 ++ part14_6 ++ part14_7 ++ part14_8 ++ part14_9 ++ part14_10 ++ part14_11

end Airbender.Compiler.UnifiedPrefixNative.Column1
