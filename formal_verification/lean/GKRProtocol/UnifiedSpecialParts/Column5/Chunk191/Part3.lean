import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24472 : Setup.Block := original.get ⟨24, by decide +kernel⟩

column_blocks_part part24472_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24472 stop 24473
noncomputable def destination24472_0 : Setup.Block := part24472_0.get ⟨0, by decide +kernel⟩

noncomputable def target24472 : List Setup.Block := part24472_0

theorem follows24472 : blockTargetsFollow source24472 0 target24472 :=
  And.intro (by
    intro index bounded
    change source24472.get? (0 + index) = destination24472_0.get? index
    have same : source24472 = destination24472_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24472 : (target24472.map Setup.Block.length).sum = source24472.length := by decide +kernel

noncomputable def source24473 : Setup.Block := original.get ⟨25, by decide +kernel⟩

column_blocks_part part24473_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24473 stop 24474
noncomputable def destination24473_0 : Setup.Block := part24473_0.get ⟨0, by decide +kernel⟩

noncomputable def target24473 : List Setup.Block := part24473_0

theorem follows24473 : blockTargetsFollow source24473 0 target24473 :=
  And.intro (by
    intro index bounded
    change source24473.get? (0 + index) = destination24473_0.get? index
    have same : source24473 = destination24473_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24473 : (target24473.map Setup.Block.length).sum = source24473.length := by decide +kernel

noncomputable def source24474 : Setup.Block := original.get ⟨26, by decide +kernel⟩

column_blocks_part part24474_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24474 stop 24475
noncomputable def destination24474_0 : Setup.Block := part24474_0.get ⟨0, by decide +kernel⟩

noncomputable def target24474 : List Setup.Block := part24474_0

theorem follows24474 : blockTargetsFollow source24474 0 target24474 :=
  And.intro (by
    intro index bounded
    change source24474.get? (0 + index) = destination24474_0.get? index
    have same : source24474 = destination24474_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24474 : (target24474.map Setup.Block.length).sum = source24474.length := by decide +kernel

noncomputable def source24475 : Setup.Block := original.get ⟨27, by decide +kernel⟩

column_blocks_part part24475_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24475 stop 24476
noncomputable def destination24475_0 : Setup.Block := part24475_0.get ⟨0, by decide +kernel⟩

noncomputable def target24475 : List Setup.Block := part24475_0

theorem follows24475 : blockTargetsFollow source24475 0 target24475 :=
  And.intro (by
    intro index bounded
    change source24475.get? (0 + index) = destination24475_0.get? index
    have same : source24475 = destination24475_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24475 : (target24475.map Setup.Block.length).sum = source24475.length := by decide +kernel

noncomputable def source24476 : Setup.Block := original.get ⟨28, by decide +kernel⟩

column_blocks_part part24476_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24476 stop 24477
noncomputable def destination24476_0 : Setup.Block := part24476_0.get ⟨0, by decide +kernel⟩

noncomputable def target24476 : List Setup.Block := part24476_0

theorem follows24476 : blockTargetsFollow source24476 0 target24476 :=
  And.intro (by
    intro index bounded
    change source24476.get? (0 + index) = destination24476_0.get? index
    have same : source24476 = destination24476_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24476 : (target24476.map Setup.Block.length).sum = source24476.length := by decide +kernel

noncomputable def source24477 : Setup.Block := original.get ⟨29, by decide +kernel⟩

column_blocks_part part24477_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24477 stop 24478
noncomputable def destination24477_0 : Setup.Block := part24477_0.get ⟨0, by decide +kernel⟩

noncomputable def target24477 : List Setup.Block := part24477_0

theorem follows24477 : blockTargetsFollow source24477 0 target24477 :=
  And.intro (by
    intro index bounded
    change source24477.get? (0 + index) = destination24477_0.get? index
    have same : source24477 = destination24477_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24477 : (target24477.map Setup.Block.length).sum = source24477.length := by decide +kernel

noncomputable def source24478 : Setup.Block := original.get ⟨30, by decide +kernel⟩

column_blocks_part part24478_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24478 stop 24479
noncomputable def destination24478_0 : Setup.Block := part24478_0.get ⟨0, by decide +kernel⟩

noncomputable def target24478 : List Setup.Block := part24478_0

theorem follows24478 : blockTargetsFollow source24478 0 target24478 :=
  And.intro (by
    intro index bounded
    change source24478.get? (0 + index) = destination24478_0.get? index
    have same : source24478 = destination24478_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24478 : (target24478.map Setup.Block.length).sum = source24478.length := by decide +kernel

noncomputable def source24479 : Setup.Block := original.get ⟨31, by decide +kernel⟩

column_blocks_part part24479_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24479 stop 24480
noncomputable def destination24479_0 : Setup.Block := part24479_0.get ⟨0, by decide +kernel⟩

noncomputable def target24479 : List Setup.Block := part24479_0

theorem follows24479 : blockTargetsFollow source24479 0 target24479 :=
  And.intro (by
    intro index bounded
    change source24479.get? (0 + index) = destination24479_0.get? index
    have same : source24479 = destination24479_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24479 : (target24479.map Setup.Block.length).sum = source24479.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
