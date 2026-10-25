import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24464 : Setup.Block := original.get ⟨16, by decide +kernel⟩

column_blocks_part part24464_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24464 stop 24465
noncomputable def destination24464_0 : Setup.Block := part24464_0.get ⟨0, by decide +kernel⟩

noncomputable def target24464 : List Setup.Block := part24464_0

theorem follows24464 : blockTargetsFollow source24464 0 target24464 :=
  And.intro (by
    intro index bounded
    change source24464.get? (0 + index) = destination24464_0.get? index
    have same : source24464 = destination24464_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24464 : (target24464.map Setup.Block.length).sum = source24464.length := by decide +kernel

noncomputable def source24465 : Setup.Block := original.get ⟨17, by decide +kernel⟩

column_blocks_part part24465_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24465 stop 24466
noncomputable def destination24465_0 : Setup.Block := part24465_0.get ⟨0, by decide +kernel⟩

noncomputable def target24465 : List Setup.Block := part24465_0

theorem follows24465 : blockTargetsFollow source24465 0 target24465 :=
  And.intro (by
    intro index bounded
    change source24465.get? (0 + index) = destination24465_0.get? index
    have same : source24465 = destination24465_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24465 : (target24465.map Setup.Block.length).sum = source24465.length := by decide +kernel

noncomputable def source24466 : Setup.Block := original.get ⟨18, by decide +kernel⟩

column_blocks_part part24466_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24466 stop 24467
noncomputable def destination24466_0 : Setup.Block := part24466_0.get ⟨0, by decide +kernel⟩

noncomputable def target24466 : List Setup.Block := part24466_0

theorem follows24466 : blockTargetsFollow source24466 0 target24466 :=
  And.intro (by
    intro index bounded
    change source24466.get? (0 + index) = destination24466_0.get? index
    have same : source24466 = destination24466_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24466 : (target24466.map Setup.Block.length).sum = source24466.length := by decide +kernel

noncomputable def source24467 : Setup.Block := original.get ⟨19, by decide +kernel⟩

column_blocks_part part24467_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24467 stop 24468
noncomputable def destination24467_0 : Setup.Block := part24467_0.get ⟨0, by decide +kernel⟩

noncomputable def target24467 : List Setup.Block := part24467_0

theorem follows24467 : blockTargetsFollow source24467 0 target24467 :=
  And.intro (by
    intro index bounded
    change source24467.get? (0 + index) = destination24467_0.get? index
    have same : source24467 = destination24467_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24467 : (target24467.map Setup.Block.length).sum = source24467.length := by decide +kernel

noncomputable def source24468 : Setup.Block := original.get ⟨20, by decide +kernel⟩

column_blocks_part part24468_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24468 stop 24469
noncomputable def destination24468_0 : Setup.Block := part24468_0.get ⟨0, by decide +kernel⟩

noncomputable def target24468 : List Setup.Block := part24468_0

theorem follows24468 : blockTargetsFollow source24468 0 target24468 :=
  And.intro (by
    intro index bounded
    change source24468.get? (0 + index) = destination24468_0.get? index
    have same : source24468 = destination24468_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24468 : (target24468.map Setup.Block.length).sum = source24468.length := by decide +kernel

noncomputable def source24469 : Setup.Block := original.get ⟨21, by decide +kernel⟩

column_blocks_part part24469_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24469 stop 24470
noncomputable def destination24469_0 : Setup.Block := part24469_0.get ⟨0, by decide +kernel⟩

noncomputable def target24469 : List Setup.Block := part24469_0

theorem follows24469 : blockTargetsFollow source24469 0 target24469 :=
  And.intro (by
    intro index bounded
    change source24469.get? (0 + index) = destination24469_0.get? index
    have same : source24469 = destination24469_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24469 : (target24469.map Setup.Block.length).sum = source24469.length := by decide +kernel

noncomputable def source24470 : Setup.Block := original.get ⟨22, by decide +kernel⟩

column_blocks_part part24470_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24470 stop 24471
noncomputable def destination24470_0 : Setup.Block := part24470_0.get ⟨0, by decide +kernel⟩

noncomputable def target24470 : List Setup.Block := part24470_0

theorem follows24470 : blockTargetsFollow source24470 0 target24470 :=
  And.intro (by
    intro index bounded
    change source24470.get? (0 + index) = destination24470_0.get? index
    have same : source24470 = destination24470_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24470 : (target24470.map Setup.Block.length).sum = source24470.length := by decide +kernel

noncomputable def source24471 : Setup.Block := original.get ⟨23, by decide +kernel⟩

column_blocks_part part24471_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24471 stop 24472
noncomputable def destination24471_0 : Setup.Block := part24471_0.get ⟨0, by decide +kernel⟩

noncomputable def target24471 : List Setup.Block := part24471_0

theorem follows24471 : blockTargetsFollow source24471 0 target24471 :=
  And.intro (by
    intro index bounded
    change source24471.get? (0 + index) = destination24471_0.get? index
    have same : source24471 = destination24471_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24471 : (target24471.map Setup.Block.length).sum = source24471.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
