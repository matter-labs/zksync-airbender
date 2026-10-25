import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24480 : Setup.Block := original.get ⟨32, by decide +kernel⟩

column_blocks_part part24480_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24480 stop 24481
noncomputable def destination24480_0 : Setup.Block := part24480_0.get ⟨0, by decide +kernel⟩

noncomputable def target24480 : List Setup.Block := part24480_0

theorem follows24480 : blockTargetsFollow source24480 0 target24480 :=
  And.intro (by
    intro index bounded
    change source24480.get? (0 + index) = destination24480_0.get? index
    have same : source24480 = destination24480_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24480 : (target24480.map Setup.Block.length).sum = source24480.length := by decide +kernel

noncomputable def source24481 : Setup.Block := original.get ⟨33, by decide +kernel⟩

column_blocks_part part24481_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24481 stop 24482
noncomputable def destination24481_0 : Setup.Block := part24481_0.get ⟨0, by decide +kernel⟩

noncomputable def target24481 : List Setup.Block := part24481_0

theorem follows24481 : blockTargetsFollow source24481 0 target24481 :=
  And.intro (by
    intro index bounded
    change source24481.get? (0 + index) = destination24481_0.get? index
    have same : source24481 = destination24481_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24481 : (target24481.map Setup.Block.length).sum = source24481.length := by decide +kernel

noncomputable def source24482 : Setup.Block := original.get ⟨34, by decide +kernel⟩

column_blocks_part part24482_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24482 stop 24483
noncomputable def destination24482_0 : Setup.Block := part24482_0.get ⟨0, by decide +kernel⟩

noncomputable def target24482 : List Setup.Block := part24482_0

theorem follows24482 : blockTargetsFollow source24482 0 target24482 :=
  And.intro (by
    intro index bounded
    change source24482.get? (0 + index) = destination24482_0.get? index
    have same : source24482 = destination24482_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24482 : (target24482.map Setup.Block.length).sum = source24482.length := by decide +kernel

noncomputable def source24483 : Setup.Block := original.get ⟨35, by decide +kernel⟩

column_blocks_part part24483_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24483 stop 24484
noncomputable def destination24483_0 : Setup.Block := part24483_0.get ⟨0, by decide +kernel⟩

noncomputable def target24483 : List Setup.Block := part24483_0

theorem follows24483 : blockTargetsFollow source24483 0 target24483 :=
  And.intro (by
    intro index bounded
    change source24483.get? (0 + index) = destination24483_0.get? index
    have same : source24483 = destination24483_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24483 : (target24483.map Setup.Block.length).sum = source24483.length := by decide +kernel

noncomputable def source24484 : Setup.Block := original.get ⟨36, by decide +kernel⟩

column_blocks_part part24484_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24484 stop 24485
noncomputable def destination24484_0 : Setup.Block := part24484_0.get ⟨0, by decide +kernel⟩

noncomputable def target24484 : List Setup.Block := part24484_0

theorem follows24484 : blockTargetsFollow source24484 0 target24484 :=
  And.intro (by
    intro index bounded
    change source24484.get? (0 + index) = destination24484_0.get? index
    have same : source24484 = destination24484_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24484 : (target24484.map Setup.Block.length).sum = source24484.length := by decide +kernel

noncomputable def source24485 : Setup.Block := original.get ⟨37, by decide +kernel⟩

column_blocks_part part24485_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24485 stop 24486
noncomputable def destination24485_0 : Setup.Block := part24485_0.get ⟨0, by decide +kernel⟩

noncomputable def target24485 : List Setup.Block := part24485_0

theorem follows24485 : blockTargetsFollow source24485 0 target24485 :=
  And.intro (by
    intro index bounded
    change source24485.get? (0 + index) = destination24485_0.get? index
    have same : source24485 = destination24485_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24485 : (target24485.map Setup.Block.length).sum = source24485.length := by decide +kernel

noncomputable def source24486 : Setup.Block := original.get ⟨38, by decide +kernel⟩

column_blocks_part part24486_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24486 stop 24487
noncomputable def destination24486_0 : Setup.Block := part24486_0.get ⟨0, by decide +kernel⟩

noncomputable def target24486 : List Setup.Block := part24486_0

theorem follows24486 : blockTargetsFollow source24486 0 target24486 :=
  And.intro (by
    intro index bounded
    change source24486.get? (0 + index) = destination24486_0.get? index
    have same : source24486 = destination24486_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24486 : (target24486.map Setup.Block.length).sum = source24486.length := by decide +kernel

noncomputable def source24487 : Setup.Block := original.get ⟨39, by decide +kernel⟩

column_blocks_part part24487_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24487 stop 24488
noncomputable def destination24487_0 : Setup.Block := part24487_0.get ⟨0, by decide +kernel⟩

noncomputable def target24487 : List Setup.Block := part24487_0

theorem follows24487 : blockTargetsFollow source24487 0 target24487 :=
  And.intro (by
    intro index bounded
    change source24487.get? (0 + index) = destination24487_0.get? index
    have same : source24487 = destination24487_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24487 : (target24487.map Setup.Block.length).sum = source24487.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
