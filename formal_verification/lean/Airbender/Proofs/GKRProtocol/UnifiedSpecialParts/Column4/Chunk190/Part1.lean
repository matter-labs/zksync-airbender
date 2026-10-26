import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24328 : Setup.Block := original.get ⟨8, by decide +kernel⟩

column_blocks_part part24328_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24328 stop 24329
noncomputable def destination24328_0 : Setup.Block := part24328_0.get ⟨0, by decide +kernel⟩

noncomputable def target24328 : List Setup.Block := part24328_0

theorem follows24328 : blockTargetsFollow source24328 0 target24328 :=
  And.intro (by
    intro index bounded
    change source24328.get? (0 + index) = destination24328_0.get? index
    have same : source24328 = destination24328_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24328 : (target24328.map Setup.Block.length).sum = source24328.length := by decide +kernel

noncomputable def source24329 : Setup.Block := original.get ⟨9, by decide +kernel⟩

column_blocks_part part24329_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24329 stop 24330
noncomputable def destination24329_0 : Setup.Block := part24329_0.get ⟨0, by decide +kernel⟩

noncomputable def target24329 : List Setup.Block := part24329_0

theorem follows24329 : blockTargetsFollow source24329 0 target24329 :=
  And.intro (by
    intro index bounded
    change source24329.get? (0 + index) = destination24329_0.get? index
    have same : source24329 = destination24329_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24329 : (target24329.map Setup.Block.length).sum = source24329.length := by decide +kernel

noncomputable def source24330 : Setup.Block := original.get ⟨10, by decide +kernel⟩

column_blocks_part part24330_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24330 stop 24331
noncomputable def destination24330_0 : Setup.Block := part24330_0.get ⟨0, by decide +kernel⟩

noncomputable def target24330 : List Setup.Block := part24330_0

theorem follows24330 : blockTargetsFollow source24330 0 target24330 :=
  And.intro (by
    intro index bounded
    change source24330.get? (0 + index) = destination24330_0.get? index
    have same : source24330 = destination24330_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24330 : (target24330.map Setup.Block.length).sum = source24330.length := by decide +kernel

noncomputable def source24331 : Setup.Block := original.get ⟨11, by decide +kernel⟩

column_blocks_part part24331_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24331 stop 24332
noncomputable def destination24331_0 : Setup.Block := part24331_0.get ⟨0, by decide +kernel⟩

noncomputable def target24331 : List Setup.Block := part24331_0

theorem follows24331 : blockTargetsFollow source24331 0 target24331 :=
  And.intro (by
    intro index bounded
    change source24331.get? (0 + index) = destination24331_0.get? index
    have same : source24331 = destination24331_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24331 : (target24331.map Setup.Block.length).sum = source24331.length := by decide +kernel

noncomputable def source24332 : Setup.Block := original.get ⟨12, by decide +kernel⟩

column_blocks_part part24332_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24332 stop 24333
noncomputable def destination24332_0 : Setup.Block := part24332_0.get ⟨0, by decide +kernel⟩

noncomputable def target24332 : List Setup.Block := part24332_0

theorem follows24332 : blockTargetsFollow source24332 0 target24332 :=
  And.intro (by
    intro index bounded
    change source24332.get? (0 + index) = destination24332_0.get? index
    have same : source24332 = destination24332_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24332 : (target24332.map Setup.Block.length).sum = source24332.length := by decide +kernel

noncomputable def source24333 : Setup.Block := original.get ⟨13, by decide +kernel⟩

column_blocks_part part24333_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24333 stop 24334
noncomputable def destination24333_0 : Setup.Block := part24333_0.get ⟨0, by decide +kernel⟩

noncomputable def target24333 : List Setup.Block := part24333_0

theorem follows24333 : blockTargetsFollow source24333 0 target24333 :=
  And.intro (by
    intro index bounded
    change source24333.get? (0 + index) = destination24333_0.get? index
    have same : source24333 = destination24333_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24333 : (target24333.map Setup.Block.length).sum = source24333.length := by decide +kernel

noncomputable def source24334 : Setup.Block := original.get ⟨14, by decide +kernel⟩

column_blocks_part part24334_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24334 stop 24335
noncomputable def destination24334_0 : Setup.Block := part24334_0.get ⟨0, by decide +kernel⟩

noncomputable def target24334 : List Setup.Block := part24334_0

theorem follows24334 : blockTargetsFollow source24334 0 target24334 :=
  And.intro (by
    intro index bounded
    change source24334.get? (0 + index) = destination24334_0.get? index
    have same : source24334 = destination24334_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24334 : (target24334.map Setup.Block.length).sum = source24334.length := by decide +kernel

noncomputable def source24335 : Setup.Block := original.get ⟨15, by decide +kernel⟩

column_blocks_part part24335_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24335 stop 24336
noncomputable def destination24335_0 : Setup.Block := part24335_0.get ⟨0, by decide +kernel⟩

noncomputable def target24335 : List Setup.Block := part24335_0

theorem follows24335 : blockTargetsFollow source24335 0 target24335 :=
  And.intro (by
    intro index bounded
    change source24335.get? (0 + index) = destination24335_0.get? index
    have same : source24335 = destination24335_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24335 : (target24335.map Setup.Block.length).sum = source24335.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
