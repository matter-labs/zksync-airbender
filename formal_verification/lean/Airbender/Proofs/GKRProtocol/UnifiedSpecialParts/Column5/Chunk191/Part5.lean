import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24488 : Setup.Block := original.get ⟨40, by decide +kernel⟩

column_blocks_part part24488_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24488 stop 24489
noncomputable def destination24488_0 : Setup.Block := part24488_0.get ⟨0, by decide +kernel⟩

noncomputable def target24488 : List Setup.Block := part24488_0

theorem follows24488 : blockTargetsFollow source24488 0 target24488 :=
  And.intro (by
    intro index bounded
    change source24488.get? (0 + index) = destination24488_0.get? index
    have same : source24488 = destination24488_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24488 : (target24488.map Setup.Block.length).sum = source24488.length := by decide +kernel

noncomputable def source24489 : Setup.Block := original.get ⟨41, by decide +kernel⟩

column_blocks_part part24489_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24489 stop 24490
noncomputable def destination24489_0 : Setup.Block := part24489_0.get ⟨0, by decide +kernel⟩

noncomputable def target24489 : List Setup.Block := part24489_0

theorem follows24489 : blockTargetsFollow source24489 0 target24489 :=
  And.intro (by
    intro index bounded
    change source24489.get? (0 + index) = destination24489_0.get? index
    have same : source24489 = destination24489_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24489 : (target24489.map Setup.Block.length).sum = source24489.length := by decide +kernel

noncomputable def source24490 : Setup.Block := original.get ⟨42, by decide +kernel⟩

column_blocks_part part24490_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24490 stop 24491
noncomputable def destination24490_0 : Setup.Block := part24490_0.get ⟨0, by decide +kernel⟩

noncomputable def target24490 : List Setup.Block := part24490_0

theorem follows24490 : blockTargetsFollow source24490 0 target24490 :=
  And.intro (by
    intro index bounded
    change source24490.get? (0 + index) = destination24490_0.get? index
    have same : source24490 = destination24490_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24490 : (target24490.map Setup.Block.length).sum = source24490.length := by decide +kernel

noncomputable def source24491 : Setup.Block := original.get ⟨43, by decide +kernel⟩

column_blocks_part part24491_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24491 stop 24492
noncomputable def destination24491_0 : Setup.Block := part24491_0.get ⟨0, by decide +kernel⟩

noncomputable def target24491 : List Setup.Block := part24491_0

theorem follows24491 : blockTargetsFollow source24491 0 target24491 :=
  And.intro (by
    intro index bounded
    change source24491.get? (0 + index) = destination24491_0.get? index
    have same : source24491 = destination24491_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24491 : (target24491.map Setup.Block.length).sum = source24491.length := by decide +kernel

noncomputable def source24492 : Setup.Block := original.get ⟨44, by decide +kernel⟩

column_blocks_part part24492_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24492 stop 24493
noncomputable def destination24492_0 : Setup.Block := part24492_0.get ⟨0, by decide +kernel⟩

noncomputable def target24492 : List Setup.Block := part24492_0

theorem follows24492 : blockTargetsFollow source24492 0 target24492 :=
  And.intro (by
    intro index bounded
    change source24492.get? (0 + index) = destination24492_0.get? index
    have same : source24492 = destination24492_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24492 : (target24492.map Setup.Block.length).sum = source24492.length := by decide +kernel

noncomputable def source24493 : Setup.Block := original.get ⟨45, by decide +kernel⟩

column_blocks_part part24493_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24493 stop 24494
noncomputable def destination24493_0 : Setup.Block := part24493_0.get ⟨0, by decide +kernel⟩

noncomputable def target24493 : List Setup.Block := part24493_0

theorem follows24493 : blockTargetsFollow source24493 0 target24493 :=
  And.intro (by
    intro index bounded
    change source24493.get? (0 + index) = destination24493_0.get? index
    have same : source24493 = destination24493_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24493 : (target24493.map Setup.Block.length).sum = source24493.length := by decide +kernel

noncomputable def source24494 : Setup.Block := original.get ⟨46, by decide +kernel⟩

column_blocks_part part24494_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24494 stop 24495
noncomputable def destination24494_0 : Setup.Block := part24494_0.get ⟨0, by decide +kernel⟩

noncomputable def target24494 : List Setup.Block := part24494_0

theorem follows24494 : blockTargetsFollow source24494 0 target24494 :=
  And.intro (by
    intro index bounded
    change source24494.get? (0 + index) = destination24494_0.get? index
    have same : source24494 = destination24494_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24494 : (target24494.map Setup.Block.length).sum = source24494.length := by decide +kernel

noncomputable def source24495 : Setup.Block := original.get ⟨47, by decide +kernel⟩

column_blocks_part part24495_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24495 stop 24496
noncomputable def destination24495_0 : Setup.Block := part24495_0.get ⟨0, by decide +kernel⟩

noncomputable def target24495 : List Setup.Block := part24495_0

theorem follows24495 : blockTargetsFollow source24495 0 target24495 :=
  And.intro (by
    intro index bounded
    change source24495.get? (0 + index) = destination24495_0.get? index
    have same : source24495 = destination24495_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24495 : (target24495.map Setup.Block.length).sum = source24495.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
