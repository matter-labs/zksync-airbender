import GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24648 : Setup.Block := original.get ⟨72, by decide +kernel⟩

column_blocks_part part24648_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24648 stop 24649
noncomputable def destination24648_0 : Setup.Block := part24648_0.get ⟨0, by decide +kernel⟩

noncomputable def target24648 : List Setup.Block := part24648_0

theorem follows24648 : blockTargetsFollow source24648 0 target24648 :=
  And.intro (by
    intro index bounded
    change source24648.get? (0 + index) = destination24648_0.get? index
    have same : source24648 = destination24648_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24648 : (target24648.map Setup.Block.length).sum = source24648.length := by decide +kernel

noncomputable def source24649 : Setup.Block := original.get ⟨73, by decide +kernel⟩

column_blocks_part part24649_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24649 stop 24650
noncomputable def destination24649_0 : Setup.Block := part24649_0.get ⟨0, by decide +kernel⟩

noncomputable def target24649 : List Setup.Block := part24649_0

theorem follows24649 : blockTargetsFollow source24649 0 target24649 :=
  And.intro (by
    intro index bounded
    change source24649.get? (0 + index) = destination24649_0.get? index
    have same : source24649 = destination24649_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24649 : (target24649.map Setup.Block.length).sum = source24649.length := by decide +kernel

noncomputable def source24650 : Setup.Block := original.get ⟨74, by decide +kernel⟩

column_blocks_part part24650_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24650 stop 24651
noncomputable def destination24650_0 : Setup.Block := part24650_0.get ⟨0, by decide +kernel⟩

noncomputable def target24650 : List Setup.Block := part24650_0

theorem follows24650 : blockTargetsFollow source24650 0 target24650 :=
  And.intro (by
    intro index bounded
    change source24650.get? (0 + index) = destination24650_0.get? index
    have same : source24650 = destination24650_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24650 : (target24650.map Setup.Block.length).sum = source24650.length := by decide +kernel

noncomputable def source24651 : Setup.Block := original.get ⟨75, by decide +kernel⟩

column_blocks_part part24651_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24651 stop 24652
noncomputable def destination24651_0 : Setup.Block := part24651_0.get ⟨0, by decide +kernel⟩

noncomputable def target24651 : List Setup.Block := part24651_0

theorem follows24651 : blockTargetsFollow source24651 0 target24651 :=
  And.intro (by
    intro index bounded
    change source24651.get? (0 + index) = destination24651_0.get? index
    have same : source24651 = destination24651_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24651 : (target24651.map Setup.Block.length).sum = source24651.length := by decide +kernel

noncomputable def source24652 : Setup.Block := original.get ⟨76, by decide +kernel⟩

column_blocks_part part24652_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24652 stop 24653
noncomputable def destination24652_0 : Setup.Block := part24652_0.get ⟨0, by decide +kernel⟩

noncomputable def target24652 : List Setup.Block := part24652_0

theorem follows24652 : blockTargetsFollow source24652 0 target24652 :=
  And.intro (by
    intro index bounded
    change source24652.get? (0 + index) = destination24652_0.get? index
    have same : source24652 = destination24652_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24652 : (target24652.map Setup.Block.length).sum = source24652.length := by decide +kernel

noncomputable def source24653 : Setup.Block := original.get ⟨77, by decide +kernel⟩

column_blocks_part part24653_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24653 stop 24654
noncomputable def destination24653_0 : Setup.Block := part24653_0.get ⟨0, by decide +kernel⟩

noncomputable def target24653 : List Setup.Block := part24653_0

theorem follows24653 : blockTargetsFollow source24653 0 target24653 :=
  And.intro (by
    intro index bounded
    change source24653.get? (0 + index) = destination24653_0.get? index
    have same : source24653 = destination24653_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24653 : (target24653.map Setup.Block.length).sum = source24653.length := by decide +kernel

noncomputable def source24654 : Setup.Block := original.get ⟨78, by decide +kernel⟩

column_blocks_part part24654_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24654 stop 24655
noncomputable def destination24654_0 : Setup.Block := part24654_0.get ⟨0, by decide +kernel⟩

noncomputable def target24654 : List Setup.Block := part24654_0

theorem follows24654 : blockTargetsFollow source24654 0 target24654 :=
  And.intro (by
    intro index bounded
    change source24654.get? (0 + index) = destination24654_0.get? index
    have same : source24654 = destination24654_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24654 : (target24654.map Setup.Block.length).sum = source24654.length := by decide +kernel

noncomputable def source24655 : Setup.Block := original.get ⟨79, by decide +kernel⟩

column_blocks_part part24655_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24655 stop 24656
noncomputable def destination24655_0 : Setup.Block := part24655_0.get ⟨0, by decide +kernel⟩

noncomputable def target24655 : List Setup.Block := part24655_0

theorem follows24655 : blockTargetsFollow source24655 0 target24655 :=
  And.intro (by
    intro index bounded
    change source24655.get? (0 + index) = destination24655_0.get? index
    have same : source24655 = destination24655_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24655 : (target24655.map Setup.Block.length).sum = source24655.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
