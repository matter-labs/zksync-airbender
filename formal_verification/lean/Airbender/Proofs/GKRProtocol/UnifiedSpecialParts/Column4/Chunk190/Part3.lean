import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24344 : Setup.Block := original.get ⟨24, by decide +kernel⟩

column_blocks_part part24344_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24344 stop 24345
noncomputable def destination24344_0 : Setup.Block := part24344_0.get ⟨0, by decide +kernel⟩

noncomputable def target24344 : List Setup.Block := part24344_0

theorem follows24344 : blockTargetsFollow source24344 0 target24344 :=
  And.intro (by
    intro index bounded
    change source24344.get? (0 + index) = destination24344_0.get? index
    have same : source24344 = destination24344_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24344 : (target24344.map Setup.Block.length).sum = source24344.length := by decide +kernel

noncomputable def source24345 : Setup.Block := original.get ⟨25, by decide +kernel⟩

column_blocks_part part24345_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24345 stop 24346
noncomputable def destination24345_0 : Setup.Block := part24345_0.get ⟨0, by decide +kernel⟩

noncomputable def target24345 : List Setup.Block := part24345_0

theorem follows24345 : blockTargetsFollow source24345 0 target24345 :=
  And.intro (by
    intro index bounded
    change source24345.get? (0 + index) = destination24345_0.get? index
    have same : source24345 = destination24345_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24345 : (target24345.map Setup.Block.length).sum = source24345.length := by decide +kernel

noncomputable def source24346 : Setup.Block := original.get ⟨26, by decide +kernel⟩

column_blocks_part part24346_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24346 stop 24347
noncomputable def destination24346_0 : Setup.Block := part24346_0.get ⟨0, by decide +kernel⟩

noncomputable def target24346 : List Setup.Block := part24346_0

theorem follows24346 : blockTargetsFollow source24346 0 target24346 :=
  And.intro (by
    intro index bounded
    change source24346.get? (0 + index) = destination24346_0.get? index
    have same : source24346 = destination24346_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24346 : (target24346.map Setup.Block.length).sum = source24346.length := by decide +kernel

noncomputable def source24347 : Setup.Block := original.get ⟨27, by decide +kernel⟩

column_blocks_part part24347_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24347 stop 24348
noncomputable def destination24347_0 : Setup.Block := part24347_0.get ⟨0, by decide +kernel⟩

noncomputable def target24347 : List Setup.Block := part24347_0

theorem follows24347 : blockTargetsFollow source24347 0 target24347 :=
  And.intro (by
    intro index bounded
    change source24347.get? (0 + index) = destination24347_0.get? index
    have same : source24347 = destination24347_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24347 : (target24347.map Setup.Block.length).sum = source24347.length := by decide +kernel

noncomputable def source24348 : Setup.Block := original.get ⟨28, by decide +kernel⟩

column_blocks_part part24348_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24348 stop 24349
noncomputable def destination24348_0 : Setup.Block := part24348_0.get ⟨0, by decide +kernel⟩

noncomputable def target24348 : List Setup.Block := part24348_0

theorem follows24348 : blockTargetsFollow source24348 0 target24348 :=
  And.intro (by
    intro index bounded
    change source24348.get? (0 + index) = destination24348_0.get? index
    have same : source24348 = destination24348_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24348 : (target24348.map Setup.Block.length).sum = source24348.length := by decide +kernel

noncomputable def source24349 : Setup.Block := original.get ⟨29, by decide +kernel⟩

column_blocks_part part24349_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24349 stop 24350
noncomputable def destination24349_0 : Setup.Block := part24349_0.get ⟨0, by decide +kernel⟩

noncomputable def target24349 : List Setup.Block := part24349_0

theorem follows24349 : blockTargetsFollow source24349 0 target24349 :=
  And.intro (by
    intro index bounded
    change source24349.get? (0 + index) = destination24349_0.get? index
    have same : source24349 = destination24349_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24349 : (target24349.map Setup.Block.length).sum = source24349.length := by decide +kernel

noncomputable def source24350 : Setup.Block := original.get ⟨30, by decide +kernel⟩

column_blocks_part part24350_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24350 stop 24351
noncomputable def destination24350_0 : Setup.Block := part24350_0.get ⟨0, by decide +kernel⟩

noncomputable def target24350 : List Setup.Block := part24350_0

theorem follows24350 : blockTargetsFollow source24350 0 target24350 :=
  And.intro (by
    intro index bounded
    change source24350.get? (0 + index) = destination24350_0.get? index
    have same : source24350 = destination24350_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24350 : (target24350.map Setup.Block.length).sum = source24350.length := by decide +kernel

noncomputable def source24351 : Setup.Block := original.get ⟨31, by decide +kernel⟩

column_blocks_part part24351_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24351 stop 24352
noncomputable def destination24351_0 : Setup.Block := part24351_0.get ⟨0, by decide +kernel⟩

noncomputable def target24351 : List Setup.Block := part24351_0

theorem follows24351 : blockTargetsFollow source24351 0 target24351 :=
  And.intro (by
    intro index bounded
    change source24351.get? (0 + index) = destination24351_0.get? index
    have same : source24351 = destination24351_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24351 : (target24351.map Setup.Block.length).sum = source24351.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
