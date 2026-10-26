import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24600 : Setup.Block := original.get ⟨24, by decide +kernel⟩

column_blocks_part part24600_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24600 stop 24601
noncomputable def destination24600_0 : Setup.Block := part24600_0.get ⟨0, by decide +kernel⟩

noncomputable def target24600 : List Setup.Block := part24600_0

theorem follows24600 : blockTargetsFollow source24600 0 target24600 :=
  And.intro (by
    intro index bounded
    change source24600.get? (0 + index) = destination24600_0.get? index
    have same : source24600 = destination24600_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24600 : (target24600.map Setup.Block.length).sum = source24600.length := by decide +kernel

noncomputable def source24601 : Setup.Block := original.get ⟨25, by decide +kernel⟩

column_blocks_part part24601_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24601 stop 24602
noncomputable def destination24601_0 : Setup.Block := part24601_0.get ⟨0, by decide +kernel⟩

noncomputable def target24601 : List Setup.Block := part24601_0

theorem follows24601 : blockTargetsFollow source24601 0 target24601 :=
  And.intro (by
    intro index bounded
    change source24601.get? (0 + index) = destination24601_0.get? index
    have same : source24601 = destination24601_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24601 : (target24601.map Setup.Block.length).sum = source24601.length := by decide +kernel

noncomputable def source24602 : Setup.Block := original.get ⟨26, by decide +kernel⟩

column_blocks_part part24602_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24602 stop 24603
noncomputable def destination24602_0 : Setup.Block := part24602_0.get ⟨0, by decide +kernel⟩

noncomputable def target24602 : List Setup.Block := part24602_0

theorem follows24602 : blockTargetsFollow source24602 0 target24602 :=
  And.intro (by
    intro index bounded
    change source24602.get? (0 + index) = destination24602_0.get? index
    have same : source24602 = destination24602_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24602 : (target24602.map Setup.Block.length).sum = source24602.length := by decide +kernel

noncomputable def source24603 : Setup.Block := original.get ⟨27, by decide +kernel⟩

column_blocks_part part24603_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24603 stop 24604
noncomputable def destination24603_0 : Setup.Block := part24603_0.get ⟨0, by decide +kernel⟩

noncomputable def target24603 : List Setup.Block := part24603_0

theorem follows24603 : blockTargetsFollow source24603 0 target24603 :=
  And.intro (by
    intro index bounded
    change source24603.get? (0 + index) = destination24603_0.get? index
    have same : source24603 = destination24603_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24603 : (target24603.map Setup.Block.length).sum = source24603.length := by decide +kernel

noncomputable def source24604 : Setup.Block := original.get ⟨28, by decide +kernel⟩

column_blocks_part part24604_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24604 stop 24605
noncomputable def destination24604_0 : Setup.Block := part24604_0.get ⟨0, by decide +kernel⟩

noncomputable def target24604 : List Setup.Block := part24604_0

theorem follows24604 : blockTargetsFollow source24604 0 target24604 :=
  And.intro (by
    intro index bounded
    change source24604.get? (0 + index) = destination24604_0.get? index
    have same : source24604 = destination24604_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24604 : (target24604.map Setup.Block.length).sum = source24604.length := by decide +kernel

noncomputable def source24605 : Setup.Block := original.get ⟨29, by decide +kernel⟩

column_blocks_part part24605_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24605 stop 24606
noncomputable def destination24605_0 : Setup.Block := part24605_0.get ⟨0, by decide +kernel⟩

noncomputable def target24605 : List Setup.Block := part24605_0

theorem follows24605 : blockTargetsFollow source24605 0 target24605 :=
  And.intro (by
    intro index bounded
    change source24605.get? (0 + index) = destination24605_0.get? index
    have same : source24605 = destination24605_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24605 : (target24605.map Setup.Block.length).sum = source24605.length := by decide +kernel

noncomputable def source24606 : Setup.Block := original.get ⟨30, by decide +kernel⟩

column_blocks_part part24606_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24606 stop 24607
noncomputable def destination24606_0 : Setup.Block := part24606_0.get ⟨0, by decide +kernel⟩

noncomputable def target24606 : List Setup.Block := part24606_0

theorem follows24606 : blockTargetsFollow source24606 0 target24606 :=
  And.intro (by
    intro index bounded
    change source24606.get? (0 + index) = destination24606_0.get? index
    have same : source24606 = destination24606_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24606 : (target24606.map Setup.Block.length).sum = source24606.length := by decide +kernel

noncomputable def source24607 : Setup.Block := original.get ⟨31, by decide +kernel⟩

column_blocks_part part24607_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24607 stop 24608
noncomputable def destination24607_0 : Setup.Block := part24607_0.get ⟨0, by decide +kernel⟩

noncomputable def target24607 : List Setup.Block := part24607_0

theorem follows24607 : blockTargetsFollow source24607 0 target24607 :=
  And.intro (by
    intro index bounded
    change source24607.get? (0 + index) = destination24607_0.get? index
    have same : source24607 = destination24607_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24607 : (target24607.map Setup.Block.length).sum = source24607.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
