import GKRProtocol.UnifiedSpecialParts.Column6.Chunk189.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24192 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part24192_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24192 stop 24193
noncomputable def destination24192_0 : Setup.Block := part24192_0.get ⟨0, by decide +kernel⟩

noncomputable def target24192 : List Setup.Block := part24192_0

theorem follows24192 : blockTargetsFollow source24192 0 target24192 :=
  And.intro (by
    intro index bounded
    change source24192.get? (0 + index) = destination24192_0.get? index
    have same : source24192 = destination24192_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24192 : (target24192.map Setup.Block.length).sum = source24192.length := by decide +kernel

noncomputable def source24193 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part24193_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24193 stop 24194
noncomputable def destination24193_0 : Setup.Block := part24193_0.get ⟨0, by decide +kernel⟩

noncomputable def target24193 : List Setup.Block := part24193_0

theorem follows24193 : blockTargetsFollow source24193 0 target24193 :=
  And.intro (by
    intro index bounded
    change source24193.get? (0 + index) = destination24193_0.get? index
    have same : source24193 = destination24193_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24193 : (target24193.map Setup.Block.length).sum = source24193.length := by decide +kernel

noncomputable def source24194 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part24194_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24194 stop 24195
noncomputable def destination24194_0 : Setup.Block := part24194_0.get ⟨0, by decide +kernel⟩

noncomputable def target24194 : List Setup.Block := part24194_0

theorem follows24194 : blockTargetsFollow source24194 0 target24194 :=
  And.intro (by
    intro index bounded
    change source24194.get? (0 + index) = destination24194_0.get? index
    have same : source24194 = destination24194_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24194 : (target24194.map Setup.Block.length).sum = source24194.length := by decide +kernel

noncomputable def source24195 : Setup.Block := original.get ⟨3, by decide +kernel⟩

column_blocks_part part24195_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24195 stop 24196
noncomputable def destination24195_0 : Setup.Block := part24195_0.get ⟨0, by decide +kernel⟩

noncomputable def target24195 : List Setup.Block := part24195_0

theorem follows24195 : blockTargetsFollow source24195 0 target24195 :=
  And.intro (by
    intro index bounded
    change source24195.get? (0 + index) = destination24195_0.get? index
    have same : source24195 = destination24195_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24195 : (target24195.map Setup.Block.length).sum = source24195.length := by decide +kernel

noncomputable def source24196 : Setup.Block := original.get ⟨4, by decide +kernel⟩

column_blocks_part part24196_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24196 stop 24197
noncomputable def destination24196_0 : Setup.Block := part24196_0.get ⟨0, by decide +kernel⟩

noncomputable def target24196 : List Setup.Block := part24196_0

theorem follows24196 : blockTargetsFollow source24196 0 target24196 :=
  And.intro (by
    intro index bounded
    change source24196.get? (0 + index) = destination24196_0.get? index
    have same : source24196 = destination24196_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24196 : (target24196.map Setup.Block.length).sum = source24196.length := by decide +kernel

noncomputable def source24197 : Setup.Block := original.get ⟨5, by decide +kernel⟩

column_blocks_part part24197_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24197 stop 24198
noncomputable def destination24197_0 : Setup.Block := part24197_0.get ⟨0, by decide +kernel⟩

noncomputable def target24197 : List Setup.Block := part24197_0

theorem follows24197 : blockTargetsFollow source24197 0 target24197 :=
  And.intro (by
    intro index bounded
    change source24197.get? (0 + index) = destination24197_0.get? index
    have same : source24197 = destination24197_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24197 : (target24197.map Setup.Block.length).sum = source24197.length := by decide +kernel

noncomputable def source24198 : Setup.Block := original.get ⟨6, by decide +kernel⟩

column_blocks_part part24198_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24198 stop 24199
noncomputable def destination24198_0 : Setup.Block := part24198_0.get ⟨0, by decide +kernel⟩

noncomputable def target24198 : List Setup.Block := part24198_0

theorem follows24198 : blockTargetsFollow source24198 0 target24198 :=
  And.intro (by
    intro index bounded
    change source24198.get? (0 + index) = destination24198_0.get? index
    have same : source24198 = destination24198_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24198 : (target24198.map Setup.Block.length).sum = source24198.length := by decide +kernel

noncomputable def source24199 : Setup.Block := original.get ⟨7, by decide +kernel⟩

column_blocks_part part24199_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24199 stop 24200
noncomputable def destination24199_0 : Setup.Block := part24199_0.get ⟨0, by decide +kernel⟩

noncomputable def target24199 : List Setup.Block := part24199_0

theorem follows24199 : blockTargetsFollow source24199 0 target24199 :=
  And.intro (by
    intro index bounded
    change source24199.get? (0 + index) = destination24199_0.get? index
    have same : source24199 = destination24199_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24199 : (target24199.map Setup.Block.length).sum = source24199.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
