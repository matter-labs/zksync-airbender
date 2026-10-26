import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24352 : Setup.Block := original.get ⟨32, by decide +kernel⟩

column_blocks_part part24352_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24352 stop 24353
noncomputable def destination24352_0 : Setup.Block := part24352_0.get ⟨0, by decide +kernel⟩

noncomputable def target24352 : List Setup.Block := part24352_0

theorem follows24352 : blockTargetsFollow source24352 0 target24352 :=
  And.intro (by
    intro index bounded
    change source24352.get? (0 + index) = destination24352_0.get? index
    have same : source24352 = destination24352_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24352 : (target24352.map Setup.Block.length).sum = source24352.length := by decide +kernel

noncomputable def source24353 : Setup.Block := original.get ⟨33, by decide +kernel⟩

column_blocks_part part24353_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24353 stop 24354
noncomputable def destination24353_0 : Setup.Block := part24353_0.get ⟨0, by decide +kernel⟩

noncomputable def target24353 : List Setup.Block := part24353_0

theorem follows24353 : blockTargetsFollow source24353 0 target24353 :=
  And.intro (by
    intro index bounded
    change source24353.get? (0 + index) = destination24353_0.get? index
    have same : source24353 = destination24353_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24353 : (target24353.map Setup.Block.length).sum = source24353.length := by decide +kernel

noncomputable def source24354 : Setup.Block := original.get ⟨34, by decide +kernel⟩

column_blocks_part part24354_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24354 stop 24355
noncomputable def destination24354_0 : Setup.Block := part24354_0.get ⟨0, by decide +kernel⟩

noncomputable def target24354 : List Setup.Block := part24354_0

theorem follows24354 : blockTargetsFollow source24354 0 target24354 :=
  And.intro (by
    intro index bounded
    change source24354.get? (0 + index) = destination24354_0.get? index
    have same : source24354 = destination24354_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24354 : (target24354.map Setup.Block.length).sum = source24354.length := by decide +kernel

noncomputable def source24355 : Setup.Block := original.get ⟨35, by decide +kernel⟩

column_blocks_part part24355_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24355 stop 24356
noncomputable def destination24355_0 : Setup.Block := part24355_0.get ⟨0, by decide +kernel⟩

noncomputable def target24355 : List Setup.Block := part24355_0

theorem follows24355 : blockTargetsFollow source24355 0 target24355 :=
  And.intro (by
    intro index bounded
    change source24355.get? (0 + index) = destination24355_0.get? index
    have same : source24355 = destination24355_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24355 : (target24355.map Setup.Block.length).sum = source24355.length := by decide +kernel

noncomputable def source24356 : Setup.Block := original.get ⟨36, by decide +kernel⟩

column_blocks_part part24356_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24356 stop 24357
noncomputable def destination24356_0 : Setup.Block := part24356_0.get ⟨0, by decide +kernel⟩

noncomputable def target24356 : List Setup.Block := part24356_0

theorem follows24356 : blockTargetsFollow source24356 0 target24356 :=
  And.intro (by
    intro index bounded
    change source24356.get? (0 + index) = destination24356_0.get? index
    have same : source24356 = destination24356_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24356 : (target24356.map Setup.Block.length).sum = source24356.length := by decide +kernel

noncomputable def source24357 : Setup.Block := original.get ⟨37, by decide +kernel⟩

column_blocks_part part24357_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24357 stop 24358
noncomputable def destination24357_0 : Setup.Block := part24357_0.get ⟨0, by decide +kernel⟩

noncomputable def target24357 : List Setup.Block := part24357_0

theorem follows24357 : blockTargetsFollow source24357 0 target24357 :=
  And.intro (by
    intro index bounded
    change source24357.get? (0 + index) = destination24357_0.get? index
    have same : source24357 = destination24357_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24357 : (target24357.map Setup.Block.length).sum = source24357.length := by decide +kernel

noncomputable def source24358 : Setup.Block := original.get ⟨38, by decide +kernel⟩

column_blocks_part part24358_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24358 stop 24359
noncomputable def destination24358_0 : Setup.Block := part24358_0.get ⟨0, by decide +kernel⟩

noncomputable def target24358 : List Setup.Block := part24358_0

theorem follows24358 : blockTargetsFollow source24358 0 target24358 :=
  And.intro (by
    intro index bounded
    change source24358.get? (0 + index) = destination24358_0.get? index
    have same : source24358 = destination24358_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24358 : (target24358.map Setup.Block.length).sum = source24358.length := by decide +kernel

noncomputable def source24359 : Setup.Block := original.get ⟨39, by decide +kernel⟩

column_blocks_part part24359_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24359 stop 24360
noncomputable def destination24359_0 : Setup.Block := part24359_0.get ⟨0, by decide +kernel⟩

noncomputable def target24359 : List Setup.Block := part24359_0

theorem follows24359 : blockTargetsFollow source24359 0 target24359 :=
  And.intro (by
    intro index bounded
    change source24359.get? (0 + index) = destination24359_0.get? index
    have same : source24359 = destination24359_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24359 : (target24359.map Setup.Block.length).sum = source24359.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
