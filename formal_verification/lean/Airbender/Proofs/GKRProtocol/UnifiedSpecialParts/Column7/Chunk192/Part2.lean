import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24592 : Setup.Block := original.get ⟨16, by decide +kernel⟩

column_blocks_part part24592_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24592 stop 24593
noncomputable def destination24592_0 : Setup.Block := part24592_0.get ⟨0, by decide +kernel⟩

noncomputable def target24592 : List Setup.Block := part24592_0

theorem follows24592 : blockTargetsFollow source24592 0 target24592 :=
  And.intro (by
    intro index bounded
    change source24592.get? (0 + index) = destination24592_0.get? index
    have same : source24592 = destination24592_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24592 : (target24592.map Setup.Block.length).sum = source24592.length := by decide +kernel

noncomputable def source24593 : Setup.Block := original.get ⟨17, by decide +kernel⟩

column_blocks_part part24593_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24593 stop 24594
noncomputable def destination24593_0 : Setup.Block := part24593_0.get ⟨0, by decide +kernel⟩

noncomputable def target24593 : List Setup.Block := part24593_0

theorem follows24593 : blockTargetsFollow source24593 0 target24593 :=
  And.intro (by
    intro index bounded
    change source24593.get? (0 + index) = destination24593_0.get? index
    have same : source24593 = destination24593_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24593 : (target24593.map Setup.Block.length).sum = source24593.length := by decide +kernel

noncomputable def source24594 : Setup.Block := original.get ⟨18, by decide +kernel⟩

column_blocks_part part24594_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24594 stop 24595
noncomputable def destination24594_0 : Setup.Block := part24594_0.get ⟨0, by decide +kernel⟩

noncomputable def target24594 : List Setup.Block := part24594_0

theorem follows24594 : blockTargetsFollow source24594 0 target24594 :=
  And.intro (by
    intro index bounded
    change source24594.get? (0 + index) = destination24594_0.get? index
    have same : source24594 = destination24594_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24594 : (target24594.map Setup.Block.length).sum = source24594.length := by decide +kernel

noncomputable def source24595 : Setup.Block := original.get ⟨19, by decide +kernel⟩

column_blocks_part part24595_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24595 stop 24596
noncomputable def destination24595_0 : Setup.Block := part24595_0.get ⟨0, by decide +kernel⟩

noncomputable def target24595 : List Setup.Block := part24595_0

theorem follows24595 : blockTargetsFollow source24595 0 target24595 :=
  And.intro (by
    intro index bounded
    change source24595.get? (0 + index) = destination24595_0.get? index
    have same : source24595 = destination24595_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24595 : (target24595.map Setup.Block.length).sum = source24595.length := by decide +kernel

noncomputable def source24596 : Setup.Block := original.get ⟨20, by decide +kernel⟩

column_blocks_part part24596_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24596 stop 24597
noncomputable def destination24596_0 : Setup.Block := part24596_0.get ⟨0, by decide +kernel⟩

noncomputable def target24596 : List Setup.Block := part24596_0

theorem follows24596 : blockTargetsFollow source24596 0 target24596 :=
  And.intro (by
    intro index bounded
    change source24596.get? (0 + index) = destination24596_0.get? index
    have same : source24596 = destination24596_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24596 : (target24596.map Setup.Block.length).sum = source24596.length := by decide +kernel

noncomputable def source24597 : Setup.Block := original.get ⟨21, by decide +kernel⟩

column_blocks_part part24597_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24597 stop 24598
noncomputable def destination24597_0 : Setup.Block := part24597_0.get ⟨0, by decide +kernel⟩

noncomputable def target24597 : List Setup.Block := part24597_0

theorem follows24597 : blockTargetsFollow source24597 0 target24597 :=
  And.intro (by
    intro index bounded
    change source24597.get? (0 + index) = destination24597_0.get? index
    have same : source24597 = destination24597_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24597 : (target24597.map Setup.Block.length).sum = source24597.length := by decide +kernel

noncomputable def source24598 : Setup.Block := original.get ⟨22, by decide +kernel⟩

column_blocks_part part24598_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24598 stop 24599
noncomputable def destination24598_0 : Setup.Block := part24598_0.get ⟨0, by decide +kernel⟩

noncomputable def target24598 : List Setup.Block := part24598_0

theorem follows24598 : blockTargetsFollow source24598 0 target24598 :=
  And.intro (by
    intro index bounded
    change source24598.get? (0 + index) = destination24598_0.get? index
    have same : source24598 = destination24598_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24598 : (target24598.map Setup.Block.length).sum = source24598.length := by decide +kernel

noncomputable def source24599 : Setup.Block := original.get ⟨23, by decide +kernel⟩

column_blocks_part part24599_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24599 stop 24600
noncomputable def destination24599_0 : Setup.Block := part24599_0.get ⟨0, by decide +kernel⟩

noncomputable def target24599 : List Setup.Block := part24599_0

theorem follows24599 : blockTargetsFollow source24599 0 target24599 :=
  And.intro (by
    intro index bounded
    change source24599.get? (0 + index) = destination24599_0.get? index
    have same : source24599 = destination24599_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24599 : (target24599.map Setup.Block.length).sum = source24599.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
