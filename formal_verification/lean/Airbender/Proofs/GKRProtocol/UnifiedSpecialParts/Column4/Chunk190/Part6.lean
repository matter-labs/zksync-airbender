import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24368 : Setup.Block := original.get ⟨48, by decide +kernel⟩

column_blocks_part part24368_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24368 stop 24369
noncomputable def destination24368_0 : Setup.Block := part24368_0.get ⟨0, by decide +kernel⟩

noncomputable def target24368 : List Setup.Block := part24368_0

theorem follows24368 : blockTargetsFollow source24368 0 target24368 :=
  And.intro (by
    intro index bounded
    change source24368.get? (0 + index) = destination24368_0.get? index
    have same : source24368 = destination24368_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24368 : (target24368.map Setup.Block.length).sum = source24368.length := by decide +kernel

noncomputable def source24369 : Setup.Block := original.get ⟨49, by decide +kernel⟩

column_blocks_part part24369_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24369 stop 24370
noncomputable def destination24369_0 : Setup.Block := part24369_0.get ⟨0, by decide +kernel⟩

noncomputable def target24369 : List Setup.Block := part24369_0

theorem follows24369 : blockTargetsFollow source24369 0 target24369 :=
  And.intro (by
    intro index bounded
    change source24369.get? (0 + index) = destination24369_0.get? index
    have same : source24369 = destination24369_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24369 : (target24369.map Setup.Block.length).sum = source24369.length := by decide +kernel

noncomputable def source24370 : Setup.Block := original.get ⟨50, by decide +kernel⟩

column_blocks_part part24370_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24370 stop 24371
noncomputable def destination24370_0 : Setup.Block := part24370_0.get ⟨0, by decide +kernel⟩

noncomputable def target24370 : List Setup.Block := part24370_0

theorem follows24370 : blockTargetsFollow source24370 0 target24370 :=
  And.intro (by
    intro index bounded
    change source24370.get? (0 + index) = destination24370_0.get? index
    have same : source24370 = destination24370_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24370 : (target24370.map Setup.Block.length).sum = source24370.length := by decide +kernel

noncomputable def source24371 : Setup.Block := original.get ⟨51, by decide +kernel⟩

column_blocks_part part24371_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24371 stop 24372
noncomputable def destination24371_0 : Setup.Block := part24371_0.get ⟨0, by decide +kernel⟩

noncomputable def target24371 : List Setup.Block := part24371_0

theorem follows24371 : blockTargetsFollow source24371 0 target24371 :=
  And.intro (by
    intro index bounded
    change source24371.get? (0 + index) = destination24371_0.get? index
    have same : source24371 = destination24371_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24371 : (target24371.map Setup.Block.length).sum = source24371.length := by decide +kernel

noncomputable def source24372 : Setup.Block := original.get ⟨52, by decide +kernel⟩

column_blocks_part part24372_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24372 stop 24373
noncomputable def destination24372_0 : Setup.Block := part24372_0.get ⟨0, by decide +kernel⟩

noncomputable def target24372 : List Setup.Block := part24372_0

theorem follows24372 : blockTargetsFollow source24372 0 target24372 :=
  And.intro (by
    intro index bounded
    change source24372.get? (0 + index) = destination24372_0.get? index
    have same : source24372 = destination24372_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24372 : (target24372.map Setup.Block.length).sum = source24372.length := by decide +kernel

noncomputable def source24373 : Setup.Block := original.get ⟨53, by decide +kernel⟩

column_blocks_part part24373_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24373 stop 24374
noncomputable def destination24373_0 : Setup.Block := part24373_0.get ⟨0, by decide +kernel⟩

noncomputable def target24373 : List Setup.Block := part24373_0

theorem follows24373 : blockTargetsFollow source24373 0 target24373 :=
  And.intro (by
    intro index bounded
    change source24373.get? (0 + index) = destination24373_0.get? index
    have same : source24373 = destination24373_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24373 : (target24373.map Setup.Block.length).sum = source24373.length := by decide +kernel

noncomputable def source24374 : Setup.Block := original.get ⟨54, by decide +kernel⟩

column_blocks_part part24374_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24374 stop 24375
noncomputable def destination24374_0 : Setup.Block := part24374_0.get ⟨0, by decide +kernel⟩

noncomputable def target24374 : List Setup.Block := part24374_0

theorem follows24374 : blockTargetsFollow source24374 0 target24374 :=
  And.intro (by
    intro index bounded
    change source24374.get? (0 + index) = destination24374_0.get? index
    have same : source24374 = destination24374_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24374 : (target24374.map Setup.Block.length).sum = source24374.length := by decide +kernel

noncomputable def source24375 : Setup.Block := original.get ⟨55, by decide +kernel⟩

column_blocks_part part24375_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24375 stop 24376
noncomputable def destination24375_0 : Setup.Block := part24375_0.get ⟨0, by decide +kernel⟩

noncomputable def target24375 : List Setup.Block := part24375_0

theorem follows24375 : blockTargetsFollow source24375 0 target24375 :=
  And.intro (by
    intro index bounded
    change source24375.get? (0 + index) = destination24375_0.get? index
    have same : source24375 = destination24375_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24375 : (target24375.map Setup.Block.length).sum = source24375.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
