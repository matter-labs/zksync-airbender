import GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24576 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part24576_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24576 stop 24577
noncomputable def destination24576_0 : Setup.Block := part24576_0.get ⟨0, by decide +kernel⟩

noncomputable def target24576 : List Setup.Block := part24576_0

theorem follows24576 : blockTargetsFollow source24576 0 target24576 :=
  And.intro (by
    intro index bounded
    change source24576.get? (0 + index) = destination24576_0.get? index
    have same : source24576 = destination24576_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24576 : (target24576.map Setup.Block.length).sum = source24576.length := by decide +kernel

noncomputable def source24577 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part24577_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24577 stop 24578
noncomputable def destination24577_0 : Setup.Block := part24577_0.get ⟨0, by decide +kernel⟩

noncomputable def target24577 : List Setup.Block := part24577_0

theorem follows24577 : blockTargetsFollow source24577 0 target24577 :=
  And.intro (by
    intro index bounded
    change source24577.get? (0 + index) = destination24577_0.get? index
    have same : source24577 = destination24577_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24577 : (target24577.map Setup.Block.length).sum = source24577.length := by decide +kernel

noncomputable def source24578 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part24578_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24578 stop 24579
noncomputable def destination24578_0 : Setup.Block := part24578_0.get ⟨0, by decide +kernel⟩

noncomputable def target24578 : List Setup.Block := part24578_0

theorem follows24578 : blockTargetsFollow source24578 0 target24578 :=
  And.intro (by
    intro index bounded
    change source24578.get? (0 + index) = destination24578_0.get? index
    have same : source24578 = destination24578_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24578 : (target24578.map Setup.Block.length).sum = source24578.length := by decide +kernel

noncomputable def source24579 : Setup.Block := original.get ⟨3, by decide +kernel⟩

column_blocks_part part24579_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24579 stop 24580
noncomputable def destination24579_0 : Setup.Block := part24579_0.get ⟨0, by decide +kernel⟩

noncomputable def target24579 : List Setup.Block := part24579_0

theorem follows24579 : blockTargetsFollow source24579 0 target24579 :=
  And.intro (by
    intro index bounded
    change source24579.get? (0 + index) = destination24579_0.get? index
    have same : source24579 = destination24579_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24579 : (target24579.map Setup.Block.length).sum = source24579.length := by decide +kernel

noncomputable def source24580 : Setup.Block := original.get ⟨4, by decide +kernel⟩

column_blocks_part part24580_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24580 stop 24581
noncomputable def destination24580_0 : Setup.Block := part24580_0.get ⟨0, by decide +kernel⟩

noncomputable def target24580 : List Setup.Block := part24580_0

theorem follows24580 : blockTargetsFollow source24580 0 target24580 :=
  And.intro (by
    intro index bounded
    change source24580.get? (0 + index) = destination24580_0.get? index
    have same : source24580 = destination24580_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24580 : (target24580.map Setup.Block.length).sum = source24580.length := by decide +kernel

noncomputable def source24581 : Setup.Block := original.get ⟨5, by decide +kernel⟩

column_blocks_part part24581_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24581 stop 24582
noncomputable def destination24581_0 : Setup.Block := part24581_0.get ⟨0, by decide +kernel⟩

noncomputable def target24581 : List Setup.Block := part24581_0

theorem follows24581 : blockTargetsFollow source24581 0 target24581 :=
  And.intro (by
    intro index bounded
    change source24581.get? (0 + index) = destination24581_0.get? index
    have same : source24581 = destination24581_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24581 : (target24581.map Setup.Block.length).sum = source24581.length := by decide +kernel

noncomputable def source24582 : Setup.Block := original.get ⟨6, by decide +kernel⟩

column_blocks_part part24582_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24582 stop 24583
noncomputable def destination24582_0 : Setup.Block := part24582_0.get ⟨0, by decide +kernel⟩

noncomputable def target24582 : List Setup.Block := part24582_0

theorem follows24582 : blockTargetsFollow source24582 0 target24582 :=
  And.intro (by
    intro index bounded
    change source24582.get? (0 + index) = destination24582_0.get? index
    have same : source24582 = destination24582_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24582 : (target24582.map Setup.Block.length).sum = source24582.length := by decide +kernel

noncomputable def source24583 : Setup.Block := original.get ⟨7, by decide +kernel⟩

column_blocks_part part24583_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24583 stop 24584
noncomputable def destination24583_0 : Setup.Block := part24583_0.get ⟨0, by decide +kernel⟩

noncomputable def target24583 : List Setup.Block := part24583_0

theorem follows24583 : blockTargetsFollow source24583 0 target24583 :=
  And.intro (by
    intro index bounded
    change source24583.get? (0 + index) = destination24583_0.get? index
    have same : source24583 = destination24583_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24583 : (target24583.map Setup.Block.length).sum = source24583.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
