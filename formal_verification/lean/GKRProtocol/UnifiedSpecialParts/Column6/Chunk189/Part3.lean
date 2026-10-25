import GKRProtocol.UnifiedSpecialParts.Column6.Chunk189.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24216 : Setup.Block := original.get ⟨24, by decide +kernel⟩

column_blocks_part part24216_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24216 stop 24217
noncomputable def destination24216_0 : Setup.Block := part24216_0.get ⟨0, by decide +kernel⟩

noncomputable def target24216 : List Setup.Block := part24216_0

theorem follows24216 : blockTargetsFollow source24216 0 target24216 :=
  And.intro (by
    intro index bounded
    change source24216.get? (0 + index) = destination24216_0.get? index
    have same : source24216 = destination24216_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24216 : (target24216.map Setup.Block.length).sum = source24216.length := by decide +kernel

noncomputable def source24217 : Setup.Block := original.get ⟨25, by decide +kernel⟩

column_blocks_part part24217_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24217 stop 24218
noncomputable def destination24217_0 : Setup.Block := part24217_0.get ⟨0, by decide +kernel⟩

noncomputable def target24217 : List Setup.Block := part24217_0

theorem follows24217 : blockTargetsFollow source24217 0 target24217 :=
  And.intro (by
    intro index bounded
    change source24217.get? (0 + index) = destination24217_0.get? index
    have same : source24217 = destination24217_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24217 : (target24217.map Setup.Block.length).sum = source24217.length := by decide +kernel

noncomputable def source24218 : Setup.Block := original.get ⟨26, by decide +kernel⟩

column_blocks_part part24218_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24218 stop 24219
noncomputable def destination24218_0 : Setup.Block := part24218_0.get ⟨0, by decide +kernel⟩

noncomputable def target24218 : List Setup.Block := part24218_0

theorem follows24218 : blockTargetsFollow source24218 0 target24218 :=
  And.intro (by
    intro index bounded
    change source24218.get? (0 + index) = destination24218_0.get? index
    have same : source24218 = destination24218_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24218 : (target24218.map Setup.Block.length).sum = source24218.length := by decide +kernel

noncomputable def source24219 : Setup.Block := original.get ⟨27, by decide +kernel⟩

column_blocks_part part24219_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24219 stop 24220
noncomputable def destination24219_0 : Setup.Block := part24219_0.get ⟨0, by decide +kernel⟩

noncomputable def target24219 : List Setup.Block := part24219_0

theorem follows24219 : blockTargetsFollow source24219 0 target24219 :=
  And.intro (by
    intro index bounded
    change source24219.get? (0 + index) = destination24219_0.get? index
    have same : source24219 = destination24219_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24219 : (target24219.map Setup.Block.length).sum = source24219.length := by decide +kernel

noncomputable def source24220 : Setup.Block := original.get ⟨28, by decide +kernel⟩

column_blocks_part part24220_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24220 stop 24221
noncomputable def destination24220_0 : Setup.Block := part24220_0.get ⟨0, by decide +kernel⟩

noncomputable def target24220 : List Setup.Block := part24220_0

theorem follows24220 : blockTargetsFollow source24220 0 target24220 :=
  And.intro (by
    intro index bounded
    change source24220.get? (0 + index) = destination24220_0.get? index
    have same : source24220 = destination24220_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24220 : (target24220.map Setup.Block.length).sum = source24220.length := by decide +kernel

noncomputable def source24221 : Setup.Block := original.get ⟨29, by decide +kernel⟩

column_blocks_part part24221_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24221 stop 24222
noncomputable def destination24221_0 : Setup.Block := part24221_0.get ⟨0, by decide +kernel⟩

noncomputable def target24221 : List Setup.Block := part24221_0

theorem follows24221 : blockTargetsFollow source24221 0 target24221 :=
  And.intro (by
    intro index bounded
    change source24221.get? (0 + index) = destination24221_0.get? index
    have same : source24221 = destination24221_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24221 : (target24221.map Setup.Block.length).sum = source24221.length := by decide +kernel

noncomputable def source24222 : Setup.Block := original.get ⟨30, by decide +kernel⟩

column_blocks_part part24222_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24222 stop 24223
noncomputable def destination24222_0 : Setup.Block := part24222_0.get ⟨0, by decide +kernel⟩

noncomputable def target24222 : List Setup.Block := part24222_0

theorem follows24222 : blockTargetsFollow source24222 0 target24222 :=
  And.intro (by
    intro index bounded
    change source24222.get? (0 + index) = destination24222_0.get? index
    have same : source24222 = destination24222_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24222 : (target24222.map Setup.Block.length).sum = source24222.length := by decide +kernel

noncomputable def source24223 : Setup.Block := original.get ⟨31, by decide +kernel⟩

column_blocks_part part24223_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24223 stop 24224
noncomputable def destination24223_0 : Setup.Block := part24223_0.get ⟨0, by decide +kernel⟩

noncomputable def target24223 : List Setup.Block := part24223_0

theorem follows24223 : blockTargetsFollow source24223 0 target24223 :=
  And.intro (by
    intro index bounded
    change source24223.get? (0 + index) = destination24223_0.get? index
    have same : source24223 = destination24223_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24223 : (target24223.map Setup.Block.length).sum = source24223.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
