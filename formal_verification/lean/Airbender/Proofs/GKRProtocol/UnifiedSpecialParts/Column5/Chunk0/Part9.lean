import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source72 : Setup.Block := original.get ⟨72, by decide +kernel⟩

column_blocks_part part72_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 72 stop 73
noncomputable def destination72_0 : Setup.Block := part72_0.get ⟨0, by decide +kernel⟩

noncomputable def target72 : List Setup.Block := part72_0

theorem follows72 : blockTargetsFollow source72 0 target72 :=
  And.intro (by
    intro index bounded
    change source72.get? (0 + index) = destination72_0.get? index
    have same : source72 = destination72_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length72 : (target72.map Setup.Block.length).sum = source72.length := by decide +kernel

noncomputable def source73 : Setup.Block := original.get ⟨73, by decide +kernel⟩

column_blocks_part part73_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 73 stop 74
noncomputable def destination73_0 : Setup.Block := part73_0.get ⟨0, by decide +kernel⟩

noncomputable def target73 : List Setup.Block := part73_0

theorem follows73 : blockTargetsFollow source73 0 target73 :=
  And.intro (by
    intro index bounded
    change source73.get? (0 + index) = destination73_0.get? index
    have same : source73 = destination73_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length73 : (target73.map Setup.Block.length).sum = source73.length := by decide +kernel

noncomputable def source74 : Setup.Block := original.get ⟨74, by decide +kernel⟩

column_blocks_part part74_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 74 stop 75
noncomputable def destination74_0 : Setup.Block := part74_0.get ⟨0, by decide +kernel⟩

noncomputable def target74 : List Setup.Block := part74_0

theorem follows74 : blockTargetsFollow source74 0 target74 :=
  And.intro (by
    intro index bounded
    change source74.get? (0 + index) = destination74_0.get? index
    have same : source74 = destination74_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length74 : (target74.map Setup.Block.length).sum = source74.length := by decide +kernel

noncomputable def source75 : Setup.Block := original.get ⟨75, by decide +kernel⟩

column_blocks_part part75_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 75 stop 76
noncomputable def destination75_0 : Setup.Block := part75_0.get ⟨0, by decide +kernel⟩

noncomputable def target75 : List Setup.Block := part75_0

theorem follows75 : blockTargetsFollow source75 0 target75 :=
  And.intro (by
    intro index bounded
    change source75.get? (0 + index) = destination75_0.get? index
    have same : source75 = destination75_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length75 : (target75.map Setup.Block.length).sum = source75.length := by decide +kernel

noncomputable def source76 : Setup.Block := original.get ⟨76, by decide +kernel⟩

column_blocks_part part76_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 76 stop 77
noncomputable def destination76_0 : Setup.Block := part76_0.get ⟨0, by decide +kernel⟩

noncomputable def target76 : List Setup.Block := part76_0

theorem follows76 : blockTargetsFollow source76 0 target76 :=
  And.intro (by
    intro index bounded
    change source76.get? (0 + index) = destination76_0.get? index
    have same : source76 = destination76_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length76 : (target76.map Setup.Block.length).sum = source76.length := by decide +kernel

noncomputable def source77 : Setup.Block := original.get ⟨77, by decide +kernel⟩

column_blocks_part part77_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 77 stop 78
noncomputable def destination77_0 : Setup.Block := part77_0.get ⟨0, by decide +kernel⟩

noncomputable def target77 : List Setup.Block := part77_0

theorem follows77 : blockTargetsFollow source77 0 target77 :=
  And.intro (by
    intro index bounded
    change source77.get? (0 + index) = destination77_0.get? index
    have same : source77 = destination77_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length77 : (target77.map Setup.Block.length).sum = source77.length := by decide +kernel

noncomputable def source78 : Setup.Block := original.get ⟨78, by decide +kernel⟩

column_blocks_part part78_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 78 stop 79
noncomputable def destination78_0 : Setup.Block := part78_0.get ⟨0, by decide +kernel⟩

noncomputable def target78 : List Setup.Block := part78_0

theorem follows78 : blockTargetsFollow source78 0 target78 :=
  And.intro (by
    intro index bounded
    change source78.get? (0 + index) = destination78_0.get? index
    have same : source78 = destination78_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length78 : (target78.map Setup.Block.length).sum = source78.length := by decide +kernel

noncomputable def source79 : Setup.Block := original.get ⟨79, by decide +kernel⟩

column_blocks_part part79_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 79 stop 80
noncomputable def destination79_0 : Setup.Block := part79_0.get ⟨0, by decide +kernel⟩

noncomputable def target79 : List Setup.Block := part79_0

theorem follows79 : blockTargetsFollow source79 0 target79 :=
  And.intro (by
    intro index bounded
    change source79.get? (0 + index) = destination79_0.get? index
    have same : source79 = destination79_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length79 : (target79.map Setup.Block.length).sum = source79.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
