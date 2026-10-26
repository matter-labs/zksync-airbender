import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24432 : Setup.Block := original.get ⟨112, by decide +kernel⟩

column_blocks_part part24432_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 18 stop 19
noncomputable def destination24432_0 : Setup.Block := part24432_0.get ⟨0, by decide +kernel⟩

noncomputable def target24432 : List Setup.Block := part24432_0

theorem follows24432 : blockTargetsFollow source24432 0 target24432 :=
  And.intro (by
    intro index bounded
    change source24432.get? (0 + index) = destination24432_0.get? index
    have same : source24432 = destination24432_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24432 : (target24432.map Setup.Block.length).sum = source24432.length := by decide +kernel

noncomputable def source24433 : Setup.Block := original.get ⟨113, by decide +kernel⟩

column_blocks_part part24433_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 19 stop 20
noncomputable def destination24433_0 : Setup.Block := part24433_0.get ⟨0, by decide +kernel⟩

noncomputable def target24433 : List Setup.Block := part24433_0

theorem follows24433 : blockTargetsFollow source24433 0 target24433 :=
  And.intro (by
    intro index bounded
    change source24433.get? (0 + index) = destination24433_0.get? index
    have same : source24433 = destination24433_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24433 : (target24433.map Setup.Block.length).sum = source24433.length := by decide +kernel

noncomputable def source24434 : Setup.Block := original.get ⟨114, by decide +kernel⟩

column_blocks_part part24434_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 20 stop 21
noncomputable def destination24434_0 : Setup.Block := part24434_0.get ⟨0, by decide +kernel⟩

noncomputable def target24434 : List Setup.Block := part24434_0

theorem follows24434 : blockTargetsFollow source24434 0 target24434 :=
  And.intro (by
    intro index bounded
    change source24434.get? (0 + index) = destination24434_0.get? index
    have same : source24434 = destination24434_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24434 : (target24434.map Setup.Block.length).sum = source24434.length := by decide +kernel

noncomputable def source24435 : Setup.Block := original.get ⟨115, by decide +kernel⟩

column_blocks_part part24435_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 21 stop 22
noncomputable def destination24435_0 : Setup.Block := part24435_0.get ⟨0, by decide +kernel⟩

noncomputable def target24435 : List Setup.Block := part24435_0

theorem follows24435 : blockTargetsFollow source24435 0 target24435 :=
  And.intro (by
    intro index bounded
    change source24435.get? (0 + index) = destination24435_0.get? index
    have same : source24435 = destination24435_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24435 : (target24435.map Setup.Block.length).sum = source24435.length := by decide +kernel

noncomputable def source24436 : Setup.Block := original.get ⟨116, by decide +kernel⟩

column_blocks_part part24436_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 22 stop 23
noncomputable def destination24436_0 : Setup.Block := part24436_0.get ⟨0, by decide +kernel⟩

noncomputable def target24436 : List Setup.Block := part24436_0

theorem follows24436 : blockTargetsFollow source24436 0 target24436 :=
  And.intro (by
    intro index bounded
    change source24436.get? (0 + index) = destination24436_0.get? index
    have same : source24436 = destination24436_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24436 : (target24436.map Setup.Block.length).sum = source24436.length := by decide +kernel

noncomputable def source24437 : Setup.Block := original.get ⟨117, by decide +kernel⟩

column_blocks_part part24437_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 23 stop 24
noncomputable def destination24437_0 : Setup.Block := part24437_0.get ⟨0, by decide +kernel⟩

noncomputable def target24437 : List Setup.Block := part24437_0

theorem follows24437 : blockTargetsFollow source24437 0 target24437 :=
  And.intro (by
    intro index bounded
    change source24437.get? (0 + index) = destination24437_0.get? index
    have same : source24437 = destination24437_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24437 : (target24437.map Setup.Block.length).sum = source24437.length := by decide +kernel

noncomputable def source24438 : Setup.Block := original.get ⟨118, by decide +kernel⟩

column_blocks_part part24438_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 24 stop 25
noncomputable def destination24438_0 : Setup.Block := part24438_0.get ⟨0, by decide +kernel⟩

noncomputable def target24438 : List Setup.Block := part24438_0

theorem follows24438 : blockTargetsFollow source24438 0 target24438 :=
  And.intro (by
    intro index bounded
    change source24438.get? (0 + index) = destination24438_0.get? index
    have same : source24438 = destination24438_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24438 : (target24438.map Setup.Block.length).sum = source24438.length := by decide +kernel

noncomputable def source24439 : Setup.Block := original.get ⟨119, by decide +kernel⟩

column_blocks_part part24439_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 25 stop 26
noncomputable def destination24439_0 : Setup.Block := part24439_0.get ⟨0, by decide +kernel⟩

noncomputable def target24439 : List Setup.Block := part24439_0

theorem follows24439 : blockTargetsFollow source24439 0 target24439 :=
  And.intro (by
    intro index bounded
    change source24439.get? (0 + index) = destination24439_0.get? index
    have same : source24439 = destination24439_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24439 : (target24439.map Setup.Block.length).sum = source24439.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
