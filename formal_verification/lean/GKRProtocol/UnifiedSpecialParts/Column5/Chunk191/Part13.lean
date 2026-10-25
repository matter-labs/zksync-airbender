import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24552 : Setup.Block := original.get ⟨104, by decide +kernel⟩

column_blocks_part part24552_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 10 stop 11
noncomputable def destination24552_0 : Setup.Block := part24552_0.get ⟨0, by decide +kernel⟩

noncomputable def target24552 : List Setup.Block := part24552_0

theorem follows24552 : blockTargetsFollow source24552 0 target24552 :=
  And.intro (by
    intro index bounded
    change source24552.get? (0 + index) = destination24552_0.get? index
    have same : source24552 = destination24552_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24552 : (target24552.map Setup.Block.length).sum = source24552.length := by decide +kernel

noncomputable def source24553 : Setup.Block := original.get ⟨105, by decide +kernel⟩

column_blocks_part part24553_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 11 stop 12
noncomputable def destination24553_0 : Setup.Block := part24553_0.get ⟨0, by decide +kernel⟩

noncomputable def target24553 : List Setup.Block := part24553_0

theorem follows24553 : blockTargetsFollow source24553 0 target24553 :=
  And.intro (by
    intro index bounded
    change source24553.get? (0 + index) = destination24553_0.get? index
    have same : source24553 = destination24553_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24553 : (target24553.map Setup.Block.length).sum = source24553.length := by decide +kernel

noncomputable def source24554 : Setup.Block := original.get ⟨106, by decide +kernel⟩

column_blocks_part part24554_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 12 stop 13
noncomputable def destination24554_0 : Setup.Block := part24554_0.get ⟨0, by decide +kernel⟩

noncomputable def target24554 : List Setup.Block := part24554_0

theorem follows24554 : blockTargetsFollow source24554 0 target24554 :=
  And.intro (by
    intro index bounded
    change source24554.get? (0 + index) = destination24554_0.get? index
    have same : source24554 = destination24554_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24554 : (target24554.map Setup.Block.length).sum = source24554.length := by decide +kernel

noncomputable def source24555 : Setup.Block := original.get ⟨107, by decide +kernel⟩

column_blocks_part part24555_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 13 stop 14
noncomputable def destination24555_0 : Setup.Block := part24555_0.get ⟨0, by decide +kernel⟩

noncomputable def target24555 : List Setup.Block := part24555_0

theorem follows24555 : blockTargetsFollow source24555 0 target24555 :=
  And.intro (by
    intro index bounded
    change source24555.get? (0 + index) = destination24555_0.get? index
    have same : source24555 = destination24555_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24555 : (target24555.map Setup.Block.length).sum = source24555.length := by decide +kernel

noncomputable def source24556 : Setup.Block := original.get ⟨108, by decide +kernel⟩

column_blocks_part part24556_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 14 stop 15
noncomputable def destination24556_0 : Setup.Block := part24556_0.get ⟨0, by decide +kernel⟩

noncomputable def target24556 : List Setup.Block := part24556_0

theorem follows24556 : blockTargetsFollow source24556 0 target24556 :=
  And.intro (by
    intro index bounded
    change source24556.get? (0 + index) = destination24556_0.get? index
    have same : source24556 = destination24556_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24556 : (target24556.map Setup.Block.length).sum = source24556.length := by decide +kernel

noncomputable def source24557 : Setup.Block := original.get ⟨109, by decide +kernel⟩

column_blocks_part part24557_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 15 stop 16
noncomputable def destination24557_0 : Setup.Block := part24557_0.get ⟨0, by decide +kernel⟩

noncomputable def target24557 : List Setup.Block := part24557_0

theorem follows24557 : blockTargetsFollow source24557 0 target24557 :=
  And.intro (by
    intro index bounded
    change source24557.get? (0 + index) = destination24557_0.get? index
    have same : source24557 = destination24557_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24557 : (target24557.map Setup.Block.length).sum = source24557.length := by decide +kernel

noncomputable def source24558 : Setup.Block := original.get ⟨110, by decide +kernel⟩

column_blocks_part part24558_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 16 stop 17
noncomputable def destination24558_0 : Setup.Block := part24558_0.get ⟨0, by decide +kernel⟩

noncomputable def target24558 : List Setup.Block := part24558_0

theorem follows24558 : blockTargetsFollow source24558 0 target24558 :=
  And.intro (by
    intro index bounded
    change source24558.get? (0 + index) = destination24558_0.get? index
    have same : source24558 = destination24558_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24558 : (target24558.map Setup.Block.length).sum = source24558.length := by decide +kernel

noncomputable def source24559 : Setup.Block := original.get ⟨111, by decide +kernel⟩

column_blocks_part part24559_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 17 stop 18
noncomputable def destination24559_0 : Setup.Block := part24559_0.get ⟨0, by decide +kernel⟩

noncomputable def target24559 : List Setup.Block := part24559_0

theorem follows24559 : blockTargetsFollow source24559 0 target24559 :=
  And.intro (by
    intro index bounded
    change source24559.get? (0 + index) = destination24559_0.get? index
    have same : source24559 = destination24559_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24559 : (target24559.map Setup.Block.length).sum = source24559.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
