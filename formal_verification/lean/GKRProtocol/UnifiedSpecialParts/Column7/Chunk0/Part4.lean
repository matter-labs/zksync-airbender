import GKRProtocol.UnifiedSpecialParts.Column7.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source32 : Setup.Block := original.get ⟨32, by decide +kernel⟩

column_blocks_part part32_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 32 stop 33
noncomputable def destination32_0 : Setup.Block := part32_0.get ⟨0, by decide +kernel⟩

noncomputable def target32 : List Setup.Block := part32_0

theorem follows32 : blockTargetsFollow source32 0 target32 :=
  And.intro (by
    intro index bounded
    change source32.get? (0 + index) = destination32_0.get? index
    have same : source32 = destination32_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length32 : (target32.map Setup.Block.length).sum = source32.length := by decide +kernel

noncomputable def source33 : Setup.Block := original.get ⟨33, by decide +kernel⟩

column_blocks_part part33_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 33 stop 34
noncomputable def destination33_0 : Setup.Block := part33_0.get ⟨0, by decide +kernel⟩

noncomputable def target33 : List Setup.Block := part33_0

set_option maxHeartbeats 16000000 in
theorem follows33 : blockTargetsFollow source33 0 target33 :=
  And.intro (by
    intro index bounded
    change source33.get? (0 + index) = destination33_0.get? index
    have same : source33 = destination33_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length33 : (target33.map Setup.Block.length).sum = source33.length := by decide +kernel

noncomputable def source34 : Setup.Block := original.get ⟨34, by decide +kernel⟩

column_blocks_part part34_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 34 stop 35
noncomputable def destination34_0 : Setup.Block := part34_0.get ⟨0, by decide +kernel⟩

noncomputable def target34 : List Setup.Block := part34_0

theorem follows34 : blockTargetsFollow source34 0 target34 :=
  And.intro (by
    intro index bounded
    change source34.get? (0 + index) = destination34_0.get? index
    have same : source34 = destination34_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length34 : (target34.map Setup.Block.length).sum = source34.length := by decide +kernel

noncomputable def source35 : Setup.Block := original.get ⟨35, by decide +kernel⟩

column_blocks_part part35_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 35 stop 36
noncomputable def destination35_0 : Setup.Block := part35_0.get ⟨0, by decide +kernel⟩

noncomputable def target35 : List Setup.Block := part35_0

theorem follows35 : blockTargetsFollow source35 0 target35 :=
  And.intro (by
    intro index bounded
    change source35.get? (0 + index) = destination35_0.get? index
    have same : source35 = destination35_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length35 : (target35.map Setup.Block.length).sum = source35.length := by decide +kernel

noncomputable def source36 : Setup.Block := original.get ⟨36, by decide +kernel⟩

column_blocks_part part36_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 36 stop 37
noncomputable def destination36_0 : Setup.Block := part36_0.get ⟨0, by decide +kernel⟩

noncomputable def target36 : List Setup.Block := part36_0

theorem follows36 : blockTargetsFollow source36 0 target36 :=
  And.intro (by
    intro index bounded
    change source36.get? (0 + index) = destination36_0.get? index
    have same : source36 = destination36_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length36 : (target36.map Setup.Block.length).sum = source36.length := by decide +kernel

noncomputable def source37 : Setup.Block := original.get ⟨37, by decide +kernel⟩

column_blocks_part part37_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 37 stop 38
noncomputable def destination37_0 : Setup.Block := part37_0.get ⟨0, by decide +kernel⟩

noncomputable def target37 : List Setup.Block := part37_0

theorem follows37 : blockTargetsFollow source37 0 target37 :=
  And.intro (by
    intro index bounded
    change source37.get? (0 + index) = destination37_0.get? index
    have same : source37 = destination37_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length37 : (target37.map Setup.Block.length).sum = source37.length := by decide +kernel

noncomputable def source38 : Setup.Block := original.get ⟨38, by decide +kernel⟩

column_blocks_part part38_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 38 stop 39
noncomputable def destination38_0 : Setup.Block := part38_0.get ⟨0, by decide +kernel⟩

noncomputable def target38 : List Setup.Block := part38_0

theorem follows38 : blockTargetsFollow source38 0 target38 :=
  And.intro (by
    intro index bounded
    change source38.get? (0 + index) = destination38_0.get? index
    have same : source38 = destination38_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length38 : (target38.map Setup.Block.length).sum = source38.length := by decide +kernel

noncomputable def source39 : Setup.Block := original.get ⟨39, by decide +kernel⟩

column_blocks_part part39_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 39 stop 40
noncomputable def destination39_0 : Setup.Block := part39_0.get ⟨0, by decide +kernel⟩

noncomputable def target39 : List Setup.Block := part39_0

theorem follows39 : blockTargetsFollow source39 0 target39 :=
  And.intro (by
    intro index bounded
    change source39.get? (0 + index) = destination39_0.get? index
    have same : source39 = destination39_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length39 : (target39.map Setup.Block.length).sum = source39.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk0
