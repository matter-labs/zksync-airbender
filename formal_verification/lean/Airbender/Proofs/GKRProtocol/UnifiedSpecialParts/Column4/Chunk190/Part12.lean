import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24416 : Setup.Block := original.get ⟨96, by decide +kernel⟩

column_blocks_part part24416_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 2 stop 3
noncomputable def destination24416_0 : Setup.Block := part24416_0.get ⟨0, by decide +kernel⟩

noncomputable def target24416 : List Setup.Block := part24416_0

theorem follows24416 : blockTargetsFollow source24416 0 target24416 :=
  And.intro (by
    intro index bounded
    change source24416.get? (0 + index) = destination24416_0.get? index
    have same : source24416 = destination24416_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24416 : (target24416.map Setup.Block.length).sum = source24416.length := by decide +kernel

noncomputable def source24417 : Setup.Block := original.get ⟨97, by decide +kernel⟩

column_blocks_part part24417_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 3 stop 4
noncomputable def destination24417_0 : Setup.Block := part24417_0.get ⟨0, by decide +kernel⟩

noncomputable def target24417 : List Setup.Block := part24417_0

theorem follows24417 : blockTargetsFollow source24417 0 target24417 :=
  And.intro (by
    intro index bounded
    change source24417.get? (0 + index) = destination24417_0.get? index
    have same : source24417 = destination24417_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24417 : (target24417.map Setup.Block.length).sum = source24417.length := by decide +kernel

noncomputable def source24418 : Setup.Block := original.get ⟨98, by decide +kernel⟩

column_blocks_part part24418_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 4 stop 5
noncomputable def destination24418_0 : Setup.Block := part24418_0.get ⟨0, by decide +kernel⟩

noncomputable def target24418 : List Setup.Block := part24418_0

theorem follows24418 : blockTargetsFollow source24418 0 target24418 :=
  And.intro (by
    intro index bounded
    change source24418.get? (0 + index) = destination24418_0.get? index
    have same : source24418 = destination24418_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24418 : (target24418.map Setup.Block.length).sum = source24418.length := by decide +kernel

noncomputable def source24419 : Setup.Block := original.get ⟨99, by decide +kernel⟩

column_blocks_part part24419_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 5 stop 6
noncomputable def destination24419_0 : Setup.Block := part24419_0.get ⟨0, by decide +kernel⟩

noncomputable def target24419 : List Setup.Block := part24419_0

theorem follows24419 : blockTargetsFollow source24419 0 target24419 :=
  And.intro (by
    intro index bounded
    change source24419.get? (0 + index) = destination24419_0.get? index
    have same : source24419 = destination24419_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24419 : (target24419.map Setup.Block.length).sum = source24419.length := by decide +kernel

noncomputable def source24420 : Setup.Block := original.get ⟨100, by decide +kernel⟩

column_blocks_part part24420_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 6 stop 7
noncomputable def destination24420_0 : Setup.Block := part24420_0.get ⟨0, by decide +kernel⟩

noncomputable def target24420 : List Setup.Block := part24420_0

theorem follows24420 : blockTargetsFollow source24420 0 target24420 :=
  And.intro (by
    intro index bounded
    change source24420.get? (0 + index) = destination24420_0.get? index
    have same : source24420 = destination24420_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24420 : (target24420.map Setup.Block.length).sum = source24420.length := by decide +kernel

noncomputable def source24421 : Setup.Block := original.get ⟨101, by decide +kernel⟩

column_blocks_part part24421_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 7 stop 8
noncomputable def destination24421_0 : Setup.Block := part24421_0.get ⟨0, by decide +kernel⟩

noncomputable def target24421 : List Setup.Block := part24421_0

theorem follows24421 : blockTargetsFollow source24421 0 target24421 :=
  And.intro (by
    intro index bounded
    change source24421.get? (0 + index) = destination24421_0.get? index
    have same : source24421 = destination24421_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24421 : (target24421.map Setup.Block.length).sum = source24421.length := by decide +kernel

noncomputable def source24422 : Setup.Block := original.get ⟨102, by decide +kernel⟩

column_blocks_part part24422_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 8 stop 9
noncomputable def destination24422_0 : Setup.Block := part24422_0.get ⟨0, by decide +kernel⟩

noncomputable def target24422 : List Setup.Block := part24422_0

theorem follows24422 : blockTargetsFollow source24422 0 target24422 :=
  And.intro (by
    intro index bounded
    change source24422.get? (0 + index) = destination24422_0.get? index
    have same : source24422 = destination24422_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24422 : (target24422.map Setup.Block.length).sum = source24422.length := by decide +kernel

noncomputable def source24423 : Setup.Block := original.get ⟨103, by decide +kernel⟩

column_blocks_part part24423_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 9 stop 10
noncomputable def destination24423_0 : Setup.Block := part24423_0.get ⟨0, by decide +kernel⟩

noncomputable def target24423 : List Setup.Block := part24423_0

theorem follows24423 : blockTargetsFollow source24423 0 target24423 :=
  And.intro (by
    intro index bounded
    change source24423.get? (0 + index) = destination24423_0.get? index
    have same : source24423 = destination24423_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24423 : (target24423.map Setup.Block.length).sum = source24423.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
