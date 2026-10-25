import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24512 : Setup.Block := original.get ⟨64, by decide +kernel⟩

column_blocks_part part24512_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24512 stop 24513
noncomputable def destination24512_0 : Setup.Block := part24512_0.get ⟨0, by decide +kernel⟩

noncomputable def target24512 : List Setup.Block := part24512_0

theorem follows24512 : blockTargetsFollow source24512 0 target24512 :=
  And.intro (by
    intro index bounded
    change source24512.get? (0 + index) = destination24512_0.get? index
    have same : source24512 = destination24512_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24512 : (target24512.map Setup.Block.length).sum = source24512.length := by decide +kernel

noncomputable def source24513 : Setup.Block := original.get ⟨65, by decide +kernel⟩

column_blocks_part part24513_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24513 stop 24514
noncomputable def destination24513_0 : Setup.Block := part24513_0.get ⟨0, by decide +kernel⟩

noncomputable def target24513 : List Setup.Block := part24513_0

theorem follows24513 : blockTargetsFollow source24513 0 target24513 :=
  And.intro (by
    intro index bounded
    change source24513.get? (0 + index) = destination24513_0.get? index
    have same : source24513 = destination24513_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24513 : (target24513.map Setup.Block.length).sum = source24513.length := by decide +kernel

noncomputable def source24514 : Setup.Block := original.get ⟨66, by decide +kernel⟩

column_blocks_part part24514_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24514 stop 24515
noncomputable def destination24514_0 : Setup.Block := part24514_0.get ⟨0, by decide +kernel⟩

noncomputable def target24514 : List Setup.Block := part24514_0

theorem follows24514 : blockTargetsFollow source24514 0 target24514 :=
  And.intro (by
    intro index bounded
    change source24514.get? (0 + index) = destination24514_0.get? index
    have same : source24514 = destination24514_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24514 : (target24514.map Setup.Block.length).sum = source24514.length := by decide +kernel

noncomputable def source24515 : Setup.Block := original.get ⟨67, by decide +kernel⟩

column_blocks_part part24515_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24515 stop 24516
noncomputable def destination24515_0 : Setup.Block := part24515_0.get ⟨0, by decide +kernel⟩

noncomputable def target24515 : List Setup.Block := part24515_0

theorem follows24515 : blockTargetsFollow source24515 0 target24515 :=
  And.intro (by
    intro index bounded
    change source24515.get? (0 + index) = destination24515_0.get? index
    have same : source24515 = destination24515_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24515 : (target24515.map Setup.Block.length).sum = source24515.length := by decide +kernel

noncomputable def source24516 : Setup.Block := original.get ⟨68, by decide +kernel⟩

column_blocks_part part24516_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24516 stop 24517
noncomputable def destination24516_0 : Setup.Block := part24516_0.get ⟨0, by decide +kernel⟩

noncomputable def target24516 : List Setup.Block := part24516_0

theorem follows24516 : blockTargetsFollow source24516 0 target24516 :=
  And.intro (by
    intro index bounded
    change source24516.get? (0 + index) = destination24516_0.get? index
    have same : source24516 = destination24516_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24516 : (target24516.map Setup.Block.length).sum = source24516.length := by decide +kernel

noncomputable def source24517 : Setup.Block := original.get ⟨69, by decide +kernel⟩

column_blocks_part part24517_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24517 stop 24518
noncomputable def destination24517_0 : Setup.Block := part24517_0.get ⟨0, by decide +kernel⟩

noncomputable def target24517 : List Setup.Block := part24517_0

theorem follows24517 : blockTargetsFollow source24517 0 target24517 :=
  And.intro (by
    intro index bounded
    change source24517.get? (0 + index) = destination24517_0.get? index
    have same : source24517 = destination24517_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24517 : (target24517.map Setup.Block.length).sum = source24517.length := by decide +kernel

noncomputable def source24518 : Setup.Block := original.get ⟨70, by decide +kernel⟩

column_blocks_part part24518_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24518 stop 24519
noncomputable def destination24518_0 : Setup.Block := part24518_0.get ⟨0, by decide +kernel⟩

noncomputable def target24518 : List Setup.Block := part24518_0

theorem follows24518 : blockTargetsFollow source24518 0 target24518 :=
  And.intro (by
    intro index bounded
    change source24518.get? (0 + index) = destination24518_0.get? index
    have same : source24518 = destination24518_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24518 : (target24518.map Setup.Block.length).sum = source24518.length := by decide +kernel

noncomputable def source24519 : Setup.Block := original.get ⟨71, by decide +kernel⟩

column_blocks_part part24519_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24519 stop 24520
noncomputable def destination24519_0 : Setup.Block := part24519_0.get ⟨0, by decide +kernel⟩

noncomputable def target24519 : List Setup.Block := part24519_0

theorem follows24519 : blockTargetsFollow source24519 0 target24519 :=
  And.intro (by
    intro index bounded
    change source24519.get? (0 + index) = destination24519_0.get? index
    have same : source24519 = destination24519_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24519 : (target24519.map Setup.Block.length).sum = source24519.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
