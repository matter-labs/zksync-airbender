import GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24640 : Setup.Block := original.get ⟨64, by decide +kernel⟩

column_blocks_part part24640_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24640 stop 24641
noncomputable def destination24640_0 : Setup.Block := part24640_0.get ⟨0, by decide +kernel⟩

noncomputable def target24640 : List Setup.Block := part24640_0

theorem follows24640 : blockTargetsFollow source24640 0 target24640 :=
  And.intro (by
    intro index bounded
    change source24640.get? (0 + index) = destination24640_0.get? index
    have same : source24640 = destination24640_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24640 : (target24640.map Setup.Block.length).sum = source24640.length := by decide +kernel

noncomputable def source24641 : Setup.Block := original.get ⟨65, by decide +kernel⟩

column_blocks_part part24641_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24641 stop 24642
noncomputable def destination24641_0 : Setup.Block := part24641_0.get ⟨0, by decide +kernel⟩

noncomputable def target24641 : List Setup.Block := part24641_0

theorem follows24641 : blockTargetsFollow source24641 0 target24641 :=
  And.intro (by
    intro index bounded
    change source24641.get? (0 + index) = destination24641_0.get? index
    have same : source24641 = destination24641_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24641 : (target24641.map Setup.Block.length).sum = source24641.length := by decide +kernel

noncomputable def source24642 : Setup.Block := original.get ⟨66, by decide +kernel⟩

column_blocks_part part24642_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24642 stop 24643
noncomputable def destination24642_0 : Setup.Block := part24642_0.get ⟨0, by decide +kernel⟩

noncomputable def target24642 : List Setup.Block := part24642_0

theorem follows24642 : blockTargetsFollow source24642 0 target24642 :=
  And.intro (by
    intro index bounded
    change source24642.get? (0 + index) = destination24642_0.get? index
    have same : source24642 = destination24642_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24642 : (target24642.map Setup.Block.length).sum = source24642.length := by decide +kernel

noncomputable def source24643 : Setup.Block := original.get ⟨67, by decide +kernel⟩

column_blocks_part part24643_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24643 stop 24644
noncomputable def destination24643_0 : Setup.Block := part24643_0.get ⟨0, by decide +kernel⟩

noncomputable def target24643 : List Setup.Block := part24643_0

theorem follows24643 : blockTargetsFollow source24643 0 target24643 :=
  And.intro (by
    intro index bounded
    change source24643.get? (0 + index) = destination24643_0.get? index
    have same : source24643 = destination24643_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24643 : (target24643.map Setup.Block.length).sum = source24643.length := by decide +kernel

noncomputable def source24644 : Setup.Block := original.get ⟨68, by decide +kernel⟩

column_blocks_part part24644_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24644 stop 24645
noncomputable def destination24644_0 : Setup.Block := part24644_0.get ⟨0, by decide +kernel⟩

noncomputable def target24644 : List Setup.Block := part24644_0

theorem follows24644 : blockTargetsFollow source24644 0 target24644 :=
  And.intro (by
    intro index bounded
    change source24644.get? (0 + index) = destination24644_0.get? index
    have same : source24644 = destination24644_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24644 : (target24644.map Setup.Block.length).sum = source24644.length := by decide +kernel

noncomputable def source24645 : Setup.Block := original.get ⟨69, by decide +kernel⟩

column_blocks_part part24645_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24645 stop 24646
noncomputable def destination24645_0 : Setup.Block := part24645_0.get ⟨0, by decide +kernel⟩

noncomputable def target24645 : List Setup.Block := part24645_0

theorem follows24645 : blockTargetsFollow source24645 0 target24645 :=
  And.intro (by
    intro index bounded
    change source24645.get? (0 + index) = destination24645_0.get? index
    have same : source24645 = destination24645_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24645 : (target24645.map Setup.Block.length).sum = source24645.length := by decide +kernel

noncomputable def source24646 : Setup.Block := original.get ⟨70, by decide +kernel⟩

column_blocks_part part24646_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24646 stop 24647
noncomputable def destination24646_0 : Setup.Block := part24646_0.get ⟨0, by decide +kernel⟩

noncomputable def target24646 : List Setup.Block := part24646_0

theorem follows24646 : blockTargetsFollow source24646 0 target24646 :=
  And.intro (by
    intro index bounded
    change source24646.get? (0 + index) = destination24646_0.get? index
    have same : source24646 = destination24646_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24646 : (target24646.map Setup.Block.length).sum = source24646.length := by decide +kernel

noncomputable def source24647 : Setup.Block := original.get ⟨71, by decide +kernel⟩

column_blocks_part part24647_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24647 stop 24648
noncomputable def destination24647_0 : Setup.Block := part24647_0.get ⟨0, by decide +kernel⟩

noncomputable def target24647 : List Setup.Block := part24647_0

theorem follows24647 : blockTargetsFollow source24647 0 target24647 :=
  And.intro (by
    intro index bounded
    change source24647.get? (0 + index) = destination24647_0.get? index
    have same : source24647 = destination24647_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24647 : (target24647.map Setup.Block.length).sum = source24647.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
