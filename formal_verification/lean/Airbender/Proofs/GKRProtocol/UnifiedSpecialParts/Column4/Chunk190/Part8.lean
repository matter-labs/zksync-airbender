import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24384 : Setup.Block := original.get ⟨64, by decide +kernel⟩

column_blocks_part part24384_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24384 stop 24385
noncomputable def destination24384_0 : Setup.Block := part24384_0.get ⟨0, by decide +kernel⟩

noncomputable def target24384 : List Setup.Block := part24384_0

theorem follows24384 : blockTargetsFollow source24384 0 target24384 :=
  And.intro (by
    intro index bounded
    change source24384.get? (0 + index) = destination24384_0.get? index
    have same : source24384 = destination24384_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24384 : (target24384.map Setup.Block.length).sum = source24384.length := by decide +kernel

noncomputable def source24385 : Setup.Block := original.get ⟨65, by decide +kernel⟩

column_blocks_part part24385_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24385 stop 24386
noncomputable def destination24385_0 : Setup.Block := part24385_0.get ⟨0, by decide +kernel⟩

noncomputable def target24385 : List Setup.Block := part24385_0

theorem follows24385 : blockTargetsFollow source24385 0 target24385 :=
  And.intro (by
    intro index bounded
    change source24385.get? (0 + index) = destination24385_0.get? index
    have same : source24385 = destination24385_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24385 : (target24385.map Setup.Block.length).sum = source24385.length := by decide +kernel

noncomputable def source24386 : Setup.Block := original.get ⟨66, by decide +kernel⟩

column_blocks_part part24386_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24386 stop 24387
noncomputable def destination24386_0 : Setup.Block := part24386_0.get ⟨0, by decide +kernel⟩

noncomputable def target24386 : List Setup.Block := part24386_0

theorem follows24386 : blockTargetsFollow source24386 0 target24386 :=
  And.intro (by
    intro index bounded
    change source24386.get? (0 + index) = destination24386_0.get? index
    have same : source24386 = destination24386_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24386 : (target24386.map Setup.Block.length).sum = source24386.length := by decide +kernel

noncomputable def source24387 : Setup.Block := original.get ⟨67, by decide +kernel⟩

column_blocks_part part24387_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24387 stop 24388
noncomputable def destination24387_0 : Setup.Block := part24387_0.get ⟨0, by decide +kernel⟩

noncomputable def target24387 : List Setup.Block := part24387_0

theorem follows24387 : blockTargetsFollow source24387 0 target24387 :=
  And.intro (by
    intro index bounded
    change source24387.get? (0 + index) = destination24387_0.get? index
    have same : source24387 = destination24387_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24387 : (target24387.map Setup.Block.length).sum = source24387.length := by decide +kernel

noncomputable def source24388 : Setup.Block := original.get ⟨68, by decide +kernel⟩

column_blocks_part part24388_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24388 stop 24389
noncomputable def destination24388_0 : Setup.Block := part24388_0.get ⟨0, by decide +kernel⟩

noncomputable def target24388 : List Setup.Block := part24388_0

theorem follows24388 : blockTargetsFollow source24388 0 target24388 :=
  And.intro (by
    intro index bounded
    change source24388.get? (0 + index) = destination24388_0.get? index
    have same : source24388 = destination24388_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24388 : (target24388.map Setup.Block.length).sum = source24388.length := by decide +kernel

noncomputable def source24389 : Setup.Block := original.get ⟨69, by decide +kernel⟩

column_blocks_part part24389_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24389 stop 24390
noncomputable def destination24389_0 : Setup.Block := part24389_0.get ⟨0, by decide +kernel⟩

noncomputable def target24389 : List Setup.Block := part24389_0

theorem follows24389 : blockTargetsFollow source24389 0 target24389 :=
  And.intro (by
    intro index bounded
    change source24389.get? (0 + index) = destination24389_0.get? index
    have same : source24389 = destination24389_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24389 : (target24389.map Setup.Block.length).sum = source24389.length := by decide +kernel

noncomputable def source24390 : Setup.Block := original.get ⟨70, by decide +kernel⟩

column_blocks_part part24390_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24390 stop 24391
noncomputable def destination24390_0 : Setup.Block := part24390_0.get ⟨0, by decide +kernel⟩

noncomputable def target24390 : List Setup.Block := part24390_0

theorem follows24390 : blockTargetsFollow source24390 0 target24390 :=
  And.intro (by
    intro index bounded
    change source24390.get? (0 + index) = destination24390_0.get? index
    have same : source24390 = destination24390_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24390 : (target24390.map Setup.Block.length).sum = source24390.length := by decide +kernel

noncomputable def source24391 : Setup.Block := original.get ⟨71, by decide +kernel⟩

column_blocks_part part24391_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24391 stop 24392
noncomputable def destination24391_0 : Setup.Block := part24391_0.get ⟨0, by decide +kernel⟩

noncomputable def target24391 : List Setup.Block := part24391_0

theorem follows24391 : blockTargetsFollow source24391 0 target24391 :=
  And.intro (by
    intro index bounded
    change source24391.get? (0 + index) = destination24391_0.get? index
    have same : source24391 = destination24391_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24391 : (target24391.map Setup.Block.length).sum = source24391.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
