import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24528 : Setup.Block := original.get ⟨80, by decide +kernel⟩

column_blocks_part part24528_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24528 stop 24529
noncomputable def destination24528_0 : Setup.Block := part24528_0.get ⟨0, by decide +kernel⟩

noncomputable def target24528 : List Setup.Block := part24528_0

theorem follows24528 : blockTargetsFollow source24528 0 target24528 :=
  And.intro (by
    intro index bounded
    change source24528.get? (0 + index) = destination24528_0.get? index
    have same : source24528 = destination24528_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24528 : (target24528.map Setup.Block.length).sum = source24528.length := by decide +kernel

noncomputable def source24529 : Setup.Block := original.get ⟨81, by decide +kernel⟩

column_blocks_part part24529_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24529 stop 24530
noncomputable def destination24529_0 : Setup.Block := part24529_0.get ⟨0, by decide +kernel⟩

noncomputable def target24529 : List Setup.Block := part24529_0

theorem follows24529 : blockTargetsFollow source24529 0 target24529 :=
  And.intro (by
    intro index bounded
    change source24529.get? (0 + index) = destination24529_0.get? index
    have same : source24529 = destination24529_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24529 : (target24529.map Setup.Block.length).sum = source24529.length := by decide +kernel

noncomputable def source24530 : Setup.Block := original.get ⟨82, by decide +kernel⟩

column_blocks_part part24530_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24530 stop 24531
noncomputable def destination24530_0 : Setup.Block := part24530_0.get ⟨0, by decide +kernel⟩

noncomputable def target24530 : List Setup.Block := part24530_0

theorem follows24530 : blockTargetsFollow source24530 0 target24530 :=
  And.intro (by
    intro index bounded
    change source24530.get? (0 + index) = destination24530_0.get? index
    have same : source24530 = destination24530_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24530 : (target24530.map Setup.Block.length).sum = source24530.length := by decide +kernel

noncomputable def source24531 : Setup.Block := original.get ⟨83, by decide +kernel⟩

column_blocks_part part24531_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24531 stop 24532
noncomputable def destination24531_0 : Setup.Block := part24531_0.get ⟨0, by decide +kernel⟩

noncomputable def target24531 : List Setup.Block := part24531_0

theorem follows24531 : blockTargetsFollow source24531 0 target24531 :=
  And.intro (by
    intro index bounded
    change source24531.get? (0 + index) = destination24531_0.get? index
    have same : source24531 = destination24531_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24531 : (target24531.map Setup.Block.length).sum = source24531.length := by decide +kernel

noncomputable def source24532 : Setup.Block := original.get ⟨84, by decide +kernel⟩

column_blocks_part part24532_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24532 stop 24533
noncomputable def destination24532_0 : Setup.Block := part24532_0.get ⟨0, by decide +kernel⟩

noncomputable def target24532 : List Setup.Block := part24532_0

theorem follows24532 : blockTargetsFollow source24532 0 target24532 :=
  And.intro (by
    intro index bounded
    change source24532.get? (0 + index) = destination24532_0.get? index
    have same : source24532 = destination24532_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24532 : (target24532.map Setup.Block.length).sum = source24532.length := by decide +kernel

noncomputable def source24533 : Setup.Block := original.get ⟨85, by decide +kernel⟩

column_blocks_part part24533_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24533 stop 24534
noncomputable def destination24533_0 : Setup.Block := part24533_0.get ⟨0, by decide +kernel⟩

noncomputable def target24533 : List Setup.Block := part24533_0

theorem follows24533 : blockTargetsFollow source24533 0 target24533 :=
  And.intro (by
    intro index bounded
    change source24533.get? (0 + index) = destination24533_0.get? index
    have same : source24533 = destination24533_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24533 : (target24533.map Setup.Block.length).sum = source24533.length := by decide +kernel

noncomputable def source24534 : Setup.Block := original.get ⟨86, by decide +kernel⟩

column_blocks_part part24534_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24534 stop 24535
noncomputable def destination24534_0 : Setup.Block := part24534_0.get ⟨0, by decide +kernel⟩

noncomputable def target24534 : List Setup.Block := part24534_0

theorem follows24534 : blockTargetsFollow source24534 0 target24534 :=
  And.intro (by
    intro index bounded
    change source24534.get? (0 + index) = destination24534_0.get? index
    have same : source24534 = destination24534_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24534 : (target24534.map Setup.Block.length).sum = source24534.length := by decide +kernel

noncomputable def source24535 : Setup.Block := original.get ⟨87, by decide +kernel⟩

column_blocks_part part24535_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24535 stop 24536
noncomputable def destination24535_0 : Setup.Block := part24535_0.get ⟨0, by decide +kernel⟩

noncomputable def target24535 : List Setup.Block := part24535_0

theorem follows24535 : blockTargetsFollow source24535 0 target24535 :=
  And.intro (by
    intro index bounded
    change source24535.get? (0 + index) = destination24535_0.get? index
    have same : source24535 = destination24535_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24535 : (target24535.map Setup.Block.length).sum = source24535.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
