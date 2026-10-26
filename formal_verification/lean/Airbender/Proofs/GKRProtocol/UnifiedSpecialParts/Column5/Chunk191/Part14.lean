import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24560 : Setup.Block := original.get ⟨112, by decide +kernel⟩

column_blocks_part part24560_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 0 stop 1
noncomputable def destination24560_0 : Setup.Block := part24560_0.get ⟨0, by decide +kernel⟩

noncomputable def target24560 : List Setup.Block := part24560_0

theorem follows24560 : blockTargetsFollow source24560 0 target24560 :=
  And.intro (by
    intro index bounded
    change source24560.get? (0 + index) = destination24560_0.get? index
    have same : source24560 = destination24560_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24560 : (target24560.map Setup.Block.length).sum = source24560.length := by decide +kernel

noncomputable def source24561 : Setup.Block := original.get ⟨113, by decide +kernel⟩

column_blocks_part part24561_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 1 stop 2
noncomputable def destination24561_0 : Setup.Block := part24561_0.get ⟨0, by decide +kernel⟩

noncomputable def target24561 : List Setup.Block := part24561_0

theorem follows24561 : blockTargetsFollow source24561 0 target24561 :=
  And.intro (by
    intro index bounded
    change source24561.get? (0 + index) = destination24561_0.get? index
    have same : source24561 = destination24561_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24561 : (target24561.map Setup.Block.length).sum = source24561.length := by decide +kernel

noncomputable def source24562 : Setup.Block := original.get ⟨114, by decide +kernel⟩

column_blocks_part part24562_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 2 stop 3
noncomputable def destination24562_0 : Setup.Block := part24562_0.get ⟨0, by decide +kernel⟩

noncomputable def target24562 : List Setup.Block := part24562_0

theorem follows24562 : blockTargetsFollow source24562 0 target24562 :=
  And.intro (by
    intro index bounded
    change source24562.get? (0 + index) = destination24562_0.get? index
    have same : source24562 = destination24562_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24562 : (target24562.map Setup.Block.length).sum = source24562.length := by decide +kernel

noncomputable def source24563 : Setup.Block := original.get ⟨115, by decide +kernel⟩

column_blocks_part part24563_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 3 stop 4
noncomputable def destination24563_0 : Setup.Block := part24563_0.get ⟨0, by decide +kernel⟩

noncomputable def target24563 : List Setup.Block := part24563_0

theorem follows24563 : blockTargetsFollow source24563 0 target24563 :=
  And.intro (by
    intro index bounded
    change source24563.get? (0 + index) = destination24563_0.get? index
    have same : source24563 = destination24563_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24563 : (target24563.map Setup.Block.length).sum = source24563.length := by decide +kernel

noncomputable def source24564 : Setup.Block := original.get ⟨116, by decide +kernel⟩

column_blocks_part part24564_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 4 stop 5
noncomputable def destination24564_0 : Setup.Block := part24564_0.get ⟨0, by decide +kernel⟩

noncomputable def target24564 : List Setup.Block := part24564_0

theorem follows24564 : blockTargetsFollow source24564 0 target24564 :=
  And.intro (by
    intro index bounded
    change source24564.get? (0 + index) = destination24564_0.get? index
    have same : source24564 = destination24564_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24564 : (target24564.map Setup.Block.length).sum = source24564.length := by decide +kernel

noncomputable def source24565 : Setup.Block := original.get ⟨117, by decide +kernel⟩

column_blocks_part part24565_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 5 stop 6
noncomputable def destination24565_0 : Setup.Block := part24565_0.get ⟨0, by decide +kernel⟩

noncomputable def target24565 : List Setup.Block := part24565_0

theorem follows24565 : blockTargetsFollow source24565 0 target24565 :=
  And.intro (by
    intro index bounded
    change source24565.get? (0 + index) = destination24565_0.get? index
    have same : source24565 = destination24565_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24565 : (target24565.map Setup.Block.length).sum = source24565.length := by decide +kernel

noncomputable def source24566 : Setup.Block := original.get ⟨118, by decide +kernel⟩

column_blocks_part part24566_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 6 stop 7
noncomputable def destination24566_0 : Setup.Block := part24566_0.get ⟨0, by decide +kernel⟩

noncomputable def target24566 : List Setup.Block := part24566_0

theorem follows24566 : blockTargetsFollow source24566 0 target24566 :=
  And.intro (by
    intro index bounded
    change source24566.get? (0 + index) = destination24566_0.get? index
    have same : source24566 = destination24566_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24566 : (target24566.map Setup.Block.length).sum = source24566.length := by decide +kernel

noncomputable def source24567 : Setup.Block := original.get ⟨119, by decide +kernel⟩

column_blocks_part part24567_0 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 7 stop 8
noncomputable def destination24567_0 : Setup.Block := part24567_0.get ⟨0, by decide +kernel⟩

noncomputable def target24567 : List Setup.Block := part24567_0

theorem follows24567 : blockTargetsFollow source24567 0 target24567 :=
  And.intro (by
    intro index bounded
    change source24567.get? (0 + index) = destination24567_0.get? index
    have same : source24567 = destination24567_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24567 : (target24567.map Setup.Block.length).sum = source24567.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
