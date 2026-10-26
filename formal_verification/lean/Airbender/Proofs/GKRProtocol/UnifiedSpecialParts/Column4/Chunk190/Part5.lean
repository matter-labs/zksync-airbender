import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24360 : Setup.Block := original.get ⟨40, by decide +kernel⟩

column_blocks_part part24360_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24360 stop 24361
noncomputable def destination24360_0 : Setup.Block := part24360_0.get ⟨0, by decide +kernel⟩

noncomputable def target24360 : List Setup.Block := part24360_0

theorem follows24360 : blockTargetsFollow source24360 0 target24360 :=
  And.intro (by
    intro index bounded
    change source24360.get? (0 + index) = destination24360_0.get? index
    have same : source24360 = destination24360_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24360 : (target24360.map Setup.Block.length).sum = source24360.length := by decide +kernel

noncomputable def source24361 : Setup.Block := original.get ⟨41, by decide +kernel⟩

column_blocks_part part24361_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24361 stop 24362
noncomputable def destination24361_0 : Setup.Block := part24361_0.get ⟨0, by decide +kernel⟩

noncomputable def target24361 : List Setup.Block := part24361_0

theorem follows24361 : blockTargetsFollow source24361 0 target24361 :=
  And.intro (by
    intro index bounded
    change source24361.get? (0 + index) = destination24361_0.get? index
    have same : source24361 = destination24361_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24361 : (target24361.map Setup.Block.length).sum = source24361.length := by decide +kernel

noncomputable def source24362 : Setup.Block := original.get ⟨42, by decide +kernel⟩

column_blocks_part part24362_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24362 stop 24363
noncomputable def destination24362_0 : Setup.Block := part24362_0.get ⟨0, by decide +kernel⟩

noncomputable def target24362 : List Setup.Block := part24362_0

theorem follows24362 : blockTargetsFollow source24362 0 target24362 :=
  And.intro (by
    intro index bounded
    change source24362.get? (0 + index) = destination24362_0.get? index
    have same : source24362 = destination24362_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24362 : (target24362.map Setup.Block.length).sum = source24362.length := by decide +kernel

noncomputable def source24363 : Setup.Block := original.get ⟨43, by decide +kernel⟩

column_blocks_part part24363_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24363 stop 24364
noncomputable def destination24363_0 : Setup.Block := part24363_0.get ⟨0, by decide +kernel⟩

noncomputable def target24363 : List Setup.Block := part24363_0

theorem follows24363 : blockTargetsFollow source24363 0 target24363 :=
  And.intro (by
    intro index bounded
    change source24363.get? (0 + index) = destination24363_0.get? index
    have same : source24363 = destination24363_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24363 : (target24363.map Setup.Block.length).sum = source24363.length := by decide +kernel

noncomputable def source24364 : Setup.Block := original.get ⟨44, by decide +kernel⟩

column_blocks_part part24364_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24364 stop 24365
noncomputable def destination24364_0 : Setup.Block := part24364_0.get ⟨0, by decide +kernel⟩

noncomputable def target24364 : List Setup.Block := part24364_0

theorem follows24364 : blockTargetsFollow source24364 0 target24364 :=
  And.intro (by
    intro index bounded
    change source24364.get? (0 + index) = destination24364_0.get? index
    have same : source24364 = destination24364_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24364 : (target24364.map Setup.Block.length).sum = source24364.length := by decide +kernel

noncomputable def source24365 : Setup.Block := original.get ⟨45, by decide +kernel⟩

column_blocks_part part24365_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24365 stop 24366
noncomputable def destination24365_0 : Setup.Block := part24365_0.get ⟨0, by decide +kernel⟩

noncomputable def target24365 : List Setup.Block := part24365_0

theorem follows24365 : blockTargetsFollow source24365 0 target24365 :=
  And.intro (by
    intro index bounded
    change source24365.get? (0 + index) = destination24365_0.get? index
    have same : source24365 = destination24365_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24365 : (target24365.map Setup.Block.length).sum = source24365.length := by decide +kernel

noncomputable def source24366 : Setup.Block := original.get ⟨46, by decide +kernel⟩

column_blocks_part part24366_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24366 stop 24367
noncomputable def destination24366_0 : Setup.Block := part24366_0.get ⟨0, by decide +kernel⟩

noncomputable def target24366 : List Setup.Block := part24366_0

theorem follows24366 : blockTargetsFollow source24366 0 target24366 :=
  And.intro (by
    intro index bounded
    change source24366.get? (0 + index) = destination24366_0.get? index
    have same : source24366 = destination24366_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24366 : (target24366.map Setup.Block.length).sum = source24366.length := by decide +kernel

noncomputable def source24367 : Setup.Block := original.get ⟨47, by decide +kernel⟩

column_blocks_part part24367_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24367 stop 24368
noncomputable def destination24367_0 : Setup.Block := part24367_0.get ⟨0, by decide +kernel⟩

noncomputable def target24367 : List Setup.Block := part24367_0

theorem follows24367 : blockTargetsFollow source24367 0 target24367 :=
  And.intro (by
    intro index bounded
    change source24367.get? (0 + index) = destination24367_0.get? index
    have same : source24367 = destination24367_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24367 : (target24367.map Setup.Block.length).sum = source24367.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
