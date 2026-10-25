import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24568 : Setup.Block := original.get ⟨120, by decide +kernel⟩

column_blocks_part part24568_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 8 stop 9
noncomputable def destination24568_0 : Setup.Block := part24568_0.get ⟨0, by decide +kernel⟩

noncomputable def target24568 : List Setup.Block := part24568_0

theorem follows24568 : blockTargetsFollow source24568 0 target24568 :=
  And.intro (by
    intro index bounded
    change source24568.get? (0 + index) = destination24568_0.get? index
    have same : source24568 = destination24568_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24568 : (target24568.map Setup.Block.length).sum = source24568.length := by decide +kernel

noncomputable def source24569 : Setup.Block := original.get ⟨121, by decide +kernel⟩

column_blocks_part part24569_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 9 stop 10
noncomputable def destination24569_0 : Setup.Block := part24569_0.get ⟨0, by decide +kernel⟩

noncomputable def target24569 : List Setup.Block := part24569_0

theorem follows24569 : blockTargetsFollow source24569 0 target24569 :=
  And.intro (by
    intro index bounded
    change source24569.get? (0 + index) = destination24569_0.get? index
    have same : source24569 = destination24569_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24569 : (target24569.map Setup.Block.length).sum = source24569.length := by decide +kernel

noncomputable def source24570 : Setup.Block := original.get ⟨122, by decide +kernel⟩

column_blocks_part part24570_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 10 stop 11
noncomputable def destination24570_0 : Setup.Block := part24570_0.get ⟨0, by decide +kernel⟩

noncomputable def target24570 : List Setup.Block := part24570_0

theorem follows24570 : blockTargetsFollow source24570 0 target24570 :=
  And.intro (by
    intro index bounded
    change source24570.get? (0 + index) = destination24570_0.get? index
    have same : source24570 = destination24570_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24570 : (target24570.map Setup.Block.length).sum = source24570.length := by decide +kernel

noncomputable def source24571 : Setup.Block := original.get ⟨123, by decide +kernel⟩

column_blocks_part part24571_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 11 stop 12
noncomputable def destination24571_0 : Setup.Block := part24571_0.get ⟨0, by decide +kernel⟩

noncomputable def target24571 : List Setup.Block := part24571_0

theorem follows24571 : blockTargetsFollow source24571 0 target24571 :=
  And.intro (by
    intro index bounded
    change source24571.get? (0 + index) = destination24571_0.get? index
    have same : source24571 = destination24571_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24571 : (target24571.map Setup.Block.length).sum = source24571.length := by decide +kernel

noncomputable def source24572 : Setup.Block := original.get ⟨124, by decide +kernel⟩

column_blocks_part part24572_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 12 stop 13
noncomputable def destination24572_0 : Setup.Block := part24572_0.get ⟨0, by decide +kernel⟩

noncomputable def target24572 : List Setup.Block := part24572_0

theorem follows24572 : blockTargetsFollow source24572 0 target24572 :=
  And.intro (by
    intro index bounded
    change source24572.get? (0 + index) = destination24572_0.get? index
    have same : source24572 = destination24572_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24572 : (target24572.map Setup.Block.length).sum = source24572.length := by decide +kernel

noncomputable def source24573 : Setup.Block := original.get ⟨125, by decide +kernel⟩

column_blocks_part part24573_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 13 stop 14
noncomputable def destination24573_0 : Setup.Block := part24573_0.get ⟨0, by decide +kernel⟩

noncomputable def target24573 : List Setup.Block := part24573_0

theorem follows24573 : blockTargetsFollow source24573 0 target24573 :=
  And.intro (by
    intro index bounded
    change source24573.get? (0 + index) = destination24573_0.get? index
    have same : source24573 = destination24573_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24573 : (target24573.map Setup.Block.length).sum = source24573.length := by decide +kernel

noncomputable def source24574 : Setup.Block := original.get ⟨126, by decide +kernel⟩

column_blocks_part part24574_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 14 stop 15
noncomputable def destination24574_0 : Setup.Block := part24574_0.get ⟨0, by decide +kernel⟩

noncomputable def target24574 : List Setup.Block := part24574_0

theorem follows24574 : blockTargetsFollow source24574 0 target24574 :=
  And.intro (by
    intro index bounded
    change source24574.get? (0 + index) = destination24574_0.get? index
    have same : source24574 = destination24574_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24574 : (target24574.map Setup.Block.length).sum = source24574.length := by decide +kernel

noncomputable def source24575 : Setup.Block := original.get ⟨127, by decide +kernel⟩

column_blocks_part part24575_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 15 stop 16
noncomputable def destination24575_0 : Setup.Block := part24575_0.get ⟨0, by decide +kernel⟩

noncomputable def target24575 : List Setup.Block := part24575_0

theorem follows24575 : blockTargetsFollow source24575 0 target24575 :=
  And.intro (by
    intro index bounded
    change source24575.get? (0 + index) = destination24575_0.get? index
    have same : source24575 = destination24575_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24575 : (target24575.map Setup.Block.length).sum = source24575.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
