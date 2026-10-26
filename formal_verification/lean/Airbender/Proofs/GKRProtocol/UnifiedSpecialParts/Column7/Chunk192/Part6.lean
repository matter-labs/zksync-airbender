import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24624 : Setup.Block := original.get ⟨48, by decide +kernel⟩

column_blocks_part part24624_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24624 stop 24625
noncomputable def destination24624_0 : Setup.Block := part24624_0.get ⟨0, by decide +kernel⟩

noncomputable def target24624 : List Setup.Block := part24624_0

theorem follows24624 : blockTargetsFollow source24624 0 target24624 :=
  And.intro (by
    intro index bounded
    change source24624.get? (0 + index) = destination24624_0.get? index
    have same : source24624 = destination24624_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24624 : (target24624.map Setup.Block.length).sum = source24624.length := by decide +kernel

noncomputable def source24625 : Setup.Block := original.get ⟨49, by decide +kernel⟩

column_blocks_part part24625_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24625 stop 24626
noncomputable def destination24625_0 : Setup.Block := part24625_0.get ⟨0, by decide +kernel⟩

noncomputable def target24625 : List Setup.Block := part24625_0

theorem follows24625 : blockTargetsFollow source24625 0 target24625 :=
  And.intro (by
    intro index bounded
    change source24625.get? (0 + index) = destination24625_0.get? index
    have same : source24625 = destination24625_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24625 : (target24625.map Setup.Block.length).sum = source24625.length := by decide +kernel

noncomputable def source24626 : Setup.Block := original.get ⟨50, by decide +kernel⟩

column_blocks_part part24626_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24626 stop 24627
noncomputable def destination24626_0 : Setup.Block := part24626_0.get ⟨0, by decide +kernel⟩

noncomputable def target24626 : List Setup.Block := part24626_0

theorem follows24626 : blockTargetsFollow source24626 0 target24626 :=
  And.intro (by
    intro index bounded
    change source24626.get? (0 + index) = destination24626_0.get? index
    have same : source24626 = destination24626_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24626 : (target24626.map Setup.Block.length).sum = source24626.length := by decide +kernel

noncomputable def source24627 : Setup.Block := original.get ⟨51, by decide +kernel⟩

column_blocks_part part24627_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24627 stop 24628
noncomputable def destination24627_0 : Setup.Block := part24627_0.get ⟨0, by decide +kernel⟩

noncomputable def target24627 : List Setup.Block := part24627_0

theorem follows24627 : blockTargetsFollow source24627 0 target24627 :=
  And.intro (by
    intro index bounded
    change source24627.get? (0 + index) = destination24627_0.get? index
    have same : source24627 = destination24627_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24627 : (target24627.map Setup.Block.length).sum = source24627.length := by decide +kernel

noncomputable def source24628 : Setup.Block := original.get ⟨52, by decide +kernel⟩

column_blocks_part part24628_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24628 stop 24629
noncomputable def destination24628_0 : Setup.Block := part24628_0.get ⟨0, by decide +kernel⟩

noncomputable def target24628 : List Setup.Block := part24628_0

theorem follows24628 : blockTargetsFollow source24628 0 target24628 :=
  And.intro (by
    intro index bounded
    change source24628.get? (0 + index) = destination24628_0.get? index
    have same : source24628 = destination24628_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24628 : (target24628.map Setup.Block.length).sum = source24628.length := by decide +kernel

noncomputable def source24629 : Setup.Block := original.get ⟨53, by decide +kernel⟩

column_blocks_part part24629_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24629 stop 24630
noncomputable def destination24629_0 : Setup.Block := part24629_0.get ⟨0, by decide +kernel⟩

noncomputable def target24629 : List Setup.Block := part24629_0

theorem follows24629 : blockTargetsFollow source24629 0 target24629 :=
  And.intro (by
    intro index bounded
    change source24629.get? (0 + index) = destination24629_0.get? index
    have same : source24629 = destination24629_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24629 : (target24629.map Setup.Block.length).sum = source24629.length := by decide +kernel

noncomputable def source24630 : Setup.Block := original.get ⟨54, by decide +kernel⟩

column_blocks_part part24630_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24630 stop 24631
noncomputable def destination24630_0 : Setup.Block := part24630_0.get ⟨0, by decide +kernel⟩

noncomputable def target24630 : List Setup.Block := part24630_0

theorem follows24630 : blockTargetsFollow source24630 0 target24630 :=
  And.intro (by
    intro index bounded
    change source24630.get? (0 + index) = destination24630_0.get? index
    have same : source24630 = destination24630_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24630 : (target24630.map Setup.Block.length).sum = source24630.length := by decide +kernel

noncomputable def source24631 : Setup.Block := original.get ⟨55, by decide +kernel⟩

column_blocks_part part24631_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24631 stop 24632
noncomputable def destination24631_0 : Setup.Block := part24631_0.get ⟨0, by decide +kernel⟩

noncomputable def target24631 : List Setup.Block := part24631_0

theorem follows24631 : blockTargetsFollow source24631 0 target24631 :=
  And.intro (by
    intro index bounded
    change source24631.get? (0 + index) = destination24631_0.get? index
    have same : source24631 = destination24631_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24631 : (target24631.map Setup.Block.length).sum = source24631.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
