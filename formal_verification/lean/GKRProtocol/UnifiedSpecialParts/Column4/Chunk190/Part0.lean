import GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24320 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part24320_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24320 stop 24321
noncomputable def destination24320_0 : Setup.Block := part24320_0.get ⟨0, by decide +kernel⟩

noncomputable def target24320 : List Setup.Block := part24320_0

theorem follows24320 : blockTargetsFollow source24320 0 target24320 :=
  And.intro (by
    intro index bounded
    change source24320.get? (0 + index) = destination24320_0.get? index
    have same : source24320 = destination24320_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24320 : (target24320.map Setup.Block.length).sum = source24320.length := by decide +kernel

noncomputable def source24321 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part24321_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24321 stop 24322
noncomputable def destination24321_0 : Setup.Block := part24321_0.get ⟨0, by decide +kernel⟩

noncomputable def target24321 : List Setup.Block := part24321_0

theorem follows24321 : blockTargetsFollow source24321 0 target24321 :=
  And.intro (by
    intro index bounded
    change source24321.get? (0 + index) = destination24321_0.get? index
    have same : source24321 = destination24321_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24321 : (target24321.map Setup.Block.length).sum = source24321.length := by decide +kernel

noncomputable def source24322 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part24322_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24322 stop 24323
noncomputable def destination24322_0 : Setup.Block := part24322_0.get ⟨0, by decide +kernel⟩

noncomputable def target24322 : List Setup.Block := part24322_0

theorem follows24322 : blockTargetsFollow source24322 0 target24322 :=
  And.intro (by
    intro index bounded
    change source24322.get? (0 + index) = destination24322_0.get? index
    have same : source24322 = destination24322_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24322 : (target24322.map Setup.Block.length).sum = source24322.length := by decide +kernel

noncomputable def source24323 : Setup.Block := original.get ⟨3, by decide +kernel⟩

column_blocks_part part24323_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24323 stop 24324
noncomputable def destination24323_0 : Setup.Block := part24323_0.get ⟨0, by decide +kernel⟩

noncomputable def target24323 : List Setup.Block := part24323_0

theorem follows24323 : blockTargetsFollow source24323 0 target24323 :=
  And.intro (by
    intro index bounded
    change source24323.get? (0 + index) = destination24323_0.get? index
    have same : source24323 = destination24323_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24323 : (target24323.map Setup.Block.length).sum = source24323.length := by decide +kernel

noncomputable def source24324 : Setup.Block := original.get ⟨4, by decide +kernel⟩

column_blocks_part part24324_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24324 stop 24325
noncomputable def destination24324_0 : Setup.Block := part24324_0.get ⟨0, by decide +kernel⟩

noncomputable def target24324 : List Setup.Block := part24324_0

theorem follows24324 : blockTargetsFollow source24324 0 target24324 :=
  And.intro (by
    intro index bounded
    change source24324.get? (0 + index) = destination24324_0.get? index
    have same : source24324 = destination24324_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24324 : (target24324.map Setup.Block.length).sum = source24324.length := by decide +kernel

noncomputable def source24325 : Setup.Block := original.get ⟨5, by decide +kernel⟩

column_blocks_part part24325_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24325 stop 24326
noncomputable def destination24325_0 : Setup.Block := part24325_0.get ⟨0, by decide +kernel⟩

noncomputable def target24325 : List Setup.Block := part24325_0

theorem follows24325 : blockTargetsFollow source24325 0 target24325 :=
  And.intro (by
    intro index bounded
    change source24325.get? (0 + index) = destination24325_0.get? index
    have same : source24325 = destination24325_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24325 : (target24325.map Setup.Block.length).sum = source24325.length := by decide +kernel

noncomputable def source24326 : Setup.Block := original.get ⟨6, by decide +kernel⟩

column_blocks_part part24326_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24326 stop 24327
noncomputable def destination24326_0 : Setup.Block := part24326_0.get ⟨0, by decide +kernel⟩

noncomputable def target24326 : List Setup.Block := part24326_0

theorem follows24326 : blockTargetsFollow source24326 0 target24326 :=
  And.intro (by
    intro index bounded
    change source24326.get? (0 + index) = destination24326_0.get? index
    have same : source24326 = destination24326_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24326 : (target24326.map Setup.Block.length).sum = source24326.length := by decide +kernel

noncomputable def source24327 : Setup.Block := original.get ⟨7, by decide +kernel⟩

column_blocks_part part24327_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24327 stop 24328
noncomputable def destination24327_0 : Setup.Block := part24327_0.get ⟨0, by decide +kernel⟩

noncomputable def target24327 : List Setup.Block := part24327_0

theorem follows24327 : blockTargetsFollow source24327 0 target24327 :=
  And.intro (by
    intro index bounded
    change source24327.get? (0 + index) = destination24327_0.get? index
    have same : source24327 = destination24327_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24327 : (target24327.map Setup.Block.length).sum = source24327.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
