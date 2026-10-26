import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24424 : Setup.Block := original.get ⟨104, by decide +kernel⟩

column_blocks_part part24424_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 10 stop 11
noncomputable def destination24424_0 : Setup.Block := part24424_0.get ⟨0, by decide +kernel⟩

noncomputable def target24424 : List Setup.Block := part24424_0

theorem follows24424 : blockTargetsFollow source24424 0 target24424 :=
  And.intro (by
    intro index bounded
    change source24424.get? (0 + index) = destination24424_0.get? index
    have same : source24424 = destination24424_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24424 : (target24424.map Setup.Block.length).sum = source24424.length := by decide +kernel

noncomputable def source24425 : Setup.Block := original.get ⟨105, by decide +kernel⟩

column_blocks_part part24425_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 11 stop 12
noncomputable def destination24425_0 : Setup.Block := part24425_0.get ⟨0, by decide +kernel⟩

noncomputable def target24425 : List Setup.Block := part24425_0

theorem follows24425 : blockTargetsFollow source24425 0 target24425 :=
  And.intro (by
    intro index bounded
    change source24425.get? (0 + index) = destination24425_0.get? index
    have same : source24425 = destination24425_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24425 : (target24425.map Setup.Block.length).sum = source24425.length := by decide +kernel

noncomputable def source24426 : Setup.Block := original.get ⟨106, by decide +kernel⟩

column_blocks_part part24426_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 12 stop 13
noncomputable def destination24426_0 : Setup.Block := part24426_0.get ⟨0, by decide +kernel⟩

noncomputable def target24426 : List Setup.Block := part24426_0

theorem follows24426 : blockTargetsFollow source24426 0 target24426 :=
  And.intro (by
    intro index bounded
    change source24426.get? (0 + index) = destination24426_0.get? index
    have same : source24426 = destination24426_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24426 : (target24426.map Setup.Block.length).sum = source24426.length := by decide +kernel

noncomputable def source24427 : Setup.Block := original.get ⟨107, by decide +kernel⟩

column_blocks_part part24427_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 13 stop 14
noncomputable def destination24427_0 : Setup.Block := part24427_0.get ⟨0, by decide +kernel⟩

noncomputable def target24427 : List Setup.Block := part24427_0

theorem follows24427 : blockTargetsFollow source24427 0 target24427 :=
  And.intro (by
    intro index bounded
    change source24427.get? (0 + index) = destination24427_0.get? index
    have same : source24427 = destination24427_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24427 : (target24427.map Setup.Block.length).sum = source24427.length := by decide +kernel

noncomputable def source24428 : Setup.Block := original.get ⟨108, by decide +kernel⟩

column_blocks_part part24428_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 14 stop 15
noncomputable def destination24428_0 : Setup.Block := part24428_0.get ⟨0, by decide +kernel⟩

noncomputable def target24428 : List Setup.Block := part24428_0

theorem follows24428 : blockTargetsFollow source24428 0 target24428 :=
  And.intro (by
    intro index bounded
    change source24428.get? (0 + index) = destination24428_0.get? index
    have same : source24428 = destination24428_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24428 : (target24428.map Setup.Block.length).sum = source24428.length := by decide +kernel

noncomputable def source24429 : Setup.Block := original.get ⟨109, by decide +kernel⟩

column_blocks_part part24429_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 15 stop 16
noncomputable def destination24429_0 : Setup.Block := part24429_0.get ⟨0, by decide +kernel⟩

noncomputable def target24429 : List Setup.Block := part24429_0

theorem follows24429 : blockTargetsFollow source24429 0 target24429 :=
  And.intro (by
    intro index bounded
    change source24429.get? (0 + index) = destination24429_0.get? index
    have same : source24429 = destination24429_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24429 : (target24429.map Setup.Block.length).sum = source24429.length := by decide +kernel

noncomputable def source24430 : Setup.Block := original.get ⟨110, by decide +kernel⟩

column_blocks_part part24430_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 16 stop 17
noncomputable def destination24430_0 : Setup.Block := part24430_0.get ⟨0, by decide +kernel⟩

noncomputable def target24430 : List Setup.Block := part24430_0

theorem follows24430 : blockTargetsFollow source24430 0 target24430 :=
  And.intro (by
    intro index bounded
    change source24430.get? (0 + index) = destination24430_0.get? index
    have same : source24430 = destination24430_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24430 : (target24430.map Setup.Block.length).sum = source24430.length := by decide +kernel

noncomputable def source24431 : Setup.Block := original.get ⟨111, by decide +kernel⟩

column_blocks_part part24431_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 17 stop 18
noncomputable def destination24431_0 : Setup.Block := part24431_0.get ⟨0, by decide +kernel⟩

noncomputable def target24431 : List Setup.Block := part24431_0

theorem follows24431 : blockTargetsFollow source24431 0 target24431 :=
  And.intro (by
    intro index bounded
    change source24431.get? (0 + index) = destination24431_0.get? index
    have same : source24431 = destination24431_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24431 : (target24431.map Setup.Block.length).sum = source24431.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
