import GKRProtocol.UnifiedSpecialParts.Column6.Chunk189.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24256 : Setup.Block := original.get ⟨64, by decide +kernel⟩

column_blocks_part part24256_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24256 stop 24257
noncomputable def destination24256_0 : Setup.Block := part24256_0.get ⟨0, by decide +kernel⟩

noncomputable def target24256 : List Setup.Block := part24256_0

theorem follows24256 : blockTargetsFollow source24256 0 target24256 :=
  And.intro (by
    intro index bounded
    change source24256.get? (0 + index) = destination24256_0.get? index
    have same : source24256 = destination24256_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24256 : (target24256.map Setup.Block.length).sum = source24256.length := by decide +kernel

noncomputable def source24257 : Setup.Block := original.get ⟨65, by decide +kernel⟩

column_blocks_part part24257_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24257 stop 24258
noncomputable def destination24257_0 : Setup.Block := part24257_0.get ⟨0, by decide +kernel⟩

noncomputable def target24257 : List Setup.Block := part24257_0

theorem follows24257 : blockTargetsFollow source24257 0 target24257 :=
  And.intro (by
    intro index bounded
    change source24257.get? (0 + index) = destination24257_0.get? index
    have same : source24257 = destination24257_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24257 : (target24257.map Setup.Block.length).sum = source24257.length := by decide +kernel

noncomputable def source24258 : Setup.Block := original.get ⟨66, by decide +kernel⟩

column_blocks_part part24258_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24258 stop 24259
noncomputable def destination24258_0 : Setup.Block := part24258_0.get ⟨0, by decide +kernel⟩

noncomputable def target24258 : List Setup.Block := part24258_0

theorem follows24258 : blockTargetsFollow source24258 0 target24258 :=
  And.intro (by
    intro index bounded
    change source24258.get? (0 + index) = destination24258_0.get? index
    have same : source24258 = destination24258_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24258 : (target24258.map Setup.Block.length).sum = source24258.length := by decide +kernel

noncomputable def source24259 : Setup.Block := original.get ⟨67, by decide +kernel⟩

column_blocks_part part24259_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24259 stop 24260
noncomputable def destination24259_0 : Setup.Block := part24259_0.get ⟨0, by decide +kernel⟩

noncomputable def target24259 : List Setup.Block := part24259_0

theorem follows24259 : blockTargetsFollow source24259 0 target24259 :=
  And.intro (by
    intro index bounded
    change source24259.get? (0 + index) = destination24259_0.get? index
    have same : source24259 = destination24259_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24259 : (target24259.map Setup.Block.length).sum = source24259.length := by decide +kernel

noncomputable def source24260 : Setup.Block := original.get ⟨68, by decide +kernel⟩

column_blocks_part part24260_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24260 stop 24261
noncomputable def destination24260_0 : Setup.Block := part24260_0.get ⟨0, by decide +kernel⟩

noncomputable def target24260 : List Setup.Block := part24260_0

theorem follows24260 : blockTargetsFollow source24260 0 target24260 :=
  And.intro (by
    intro index bounded
    change source24260.get? (0 + index) = destination24260_0.get? index
    have same : source24260 = destination24260_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24260 : (target24260.map Setup.Block.length).sum = source24260.length := by decide +kernel

noncomputable def source24261 : Setup.Block := original.get ⟨69, by decide +kernel⟩

column_blocks_part part24261_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24261 stop 24262
noncomputable def destination24261_0 : Setup.Block := part24261_0.get ⟨0, by decide +kernel⟩

noncomputable def target24261 : List Setup.Block := part24261_0

theorem follows24261 : blockTargetsFollow source24261 0 target24261 :=
  And.intro (by
    intro index bounded
    change source24261.get? (0 + index) = destination24261_0.get? index
    have same : source24261 = destination24261_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24261 : (target24261.map Setup.Block.length).sum = source24261.length := by decide +kernel

noncomputable def source24262 : Setup.Block := original.get ⟨70, by decide +kernel⟩

column_blocks_part part24262_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24262 stop 24263
noncomputable def destination24262_0 : Setup.Block := part24262_0.get ⟨0, by decide +kernel⟩

noncomputable def target24262 : List Setup.Block := part24262_0

theorem follows24262 : blockTargetsFollow source24262 0 target24262 :=
  And.intro (by
    intro index bounded
    change source24262.get? (0 + index) = destination24262_0.get? index
    have same : source24262 = destination24262_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24262 : (target24262.map Setup.Block.length).sum = source24262.length := by decide +kernel

noncomputable def source24263 : Setup.Block := original.get ⟨71, by decide +kernel⟩

column_blocks_part part24263_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24263 stop 24264
noncomputable def destination24263_0 : Setup.Block := part24263_0.get ⟨0, by decide +kernel⟩

noncomputable def target24263 : List Setup.Block := part24263_0

theorem follows24263 : blockTargetsFollow source24263 0 target24263 :=
  And.intro (by
    intro index bounded
    change source24263.get? (0 + index) = destination24263_0.get? index
    have same : source24263 = destination24263_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24263 : (target24263.map Setup.Block.length).sum = source24263.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
