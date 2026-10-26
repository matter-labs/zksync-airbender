import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column6.Chunk189.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24200 : Setup.Block := original.get ⟨8, by decide +kernel⟩

column_blocks_part part24200_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24200 stop 24201
noncomputable def destination24200_0 : Setup.Block := part24200_0.get ⟨0, by decide +kernel⟩

noncomputable def target24200 : List Setup.Block := part24200_0

theorem follows24200 : blockTargetsFollow source24200 0 target24200 :=
  And.intro (by
    intro index bounded
    change source24200.get? (0 + index) = destination24200_0.get? index
    have same : source24200 = destination24200_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24200 : (target24200.map Setup.Block.length).sum = source24200.length := by decide +kernel

noncomputable def source24201 : Setup.Block := original.get ⟨9, by decide +kernel⟩

column_blocks_part part24201_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24201 stop 24202
noncomputable def destination24201_0 : Setup.Block := part24201_0.get ⟨0, by decide +kernel⟩

noncomputable def target24201 : List Setup.Block := part24201_0

theorem follows24201 : blockTargetsFollow source24201 0 target24201 :=
  And.intro (by
    intro index bounded
    change source24201.get? (0 + index) = destination24201_0.get? index
    have same : source24201 = destination24201_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24201 : (target24201.map Setup.Block.length).sum = source24201.length := by decide +kernel

noncomputable def source24202 : Setup.Block := original.get ⟨10, by decide +kernel⟩

column_blocks_part part24202_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24202 stop 24203
noncomputable def destination24202_0 : Setup.Block := part24202_0.get ⟨0, by decide +kernel⟩

noncomputable def target24202 : List Setup.Block := part24202_0

theorem follows24202 : blockTargetsFollow source24202 0 target24202 :=
  And.intro (by
    intro index bounded
    change source24202.get? (0 + index) = destination24202_0.get? index
    have same : source24202 = destination24202_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24202 : (target24202.map Setup.Block.length).sum = source24202.length := by decide +kernel

noncomputable def source24203 : Setup.Block := original.get ⟨11, by decide +kernel⟩

column_blocks_part part24203_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24203 stop 24204
noncomputable def destination24203_0 : Setup.Block := part24203_0.get ⟨0, by decide +kernel⟩

noncomputable def target24203 : List Setup.Block := part24203_0

theorem follows24203 : blockTargetsFollow source24203 0 target24203 :=
  And.intro (by
    intro index bounded
    change source24203.get? (0 + index) = destination24203_0.get? index
    have same : source24203 = destination24203_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24203 : (target24203.map Setup.Block.length).sum = source24203.length := by decide +kernel

noncomputable def source24204 : Setup.Block := original.get ⟨12, by decide +kernel⟩

column_blocks_part part24204_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24204 stop 24205
noncomputable def destination24204_0 : Setup.Block := part24204_0.get ⟨0, by decide +kernel⟩

noncomputable def target24204 : List Setup.Block := part24204_0

theorem follows24204 : blockTargetsFollow source24204 0 target24204 :=
  And.intro (by
    intro index bounded
    change source24204.get? (0 + index) = destination24204_0.get? index
    have same : source24204 = destination24204_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24204 : (target24204.map Setup.Block.length).sum = source24204.length := by decide +kernel

noncomputable def source24205 : Setup.Block := original.get ⟨13, by decide +kernel⟩

column_blocks_part part24205_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24205 stop 24206
noncomputable def destination24205_0 : Setup.Block := part24205_0.get ⟨0, by decide +kernel⟩

noncomputable def target24205 : List Setup.Block := part24205_0

theorem follows24205 : blockTargetsFollow source24205 0 target24205 :=
  And.intro (by
    intro index bounded
    change source24205.get? (0 + index) = destination24205_0.get? index
    have same : source24205 = destination24205_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24205 : (target24205.map Setup.Block.length).sum = source24205.length := by decide +kernel

noncomputable def source24206 : Setup.Block := original.get ⟨14, by decide +kernel⟩

column_blocks_part part24206_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24206 stop 24207
noncomputable def destination24206_0 : Setup.Block := part24206_0.get ⟨0, by decide +kernel⟩

noncomputable def target24206 : List Setup.Block := part24206_0

theorem follows24206 : blockTargetsFollow source24206 0 target24206 :=
  And.intro (by
    intro index bounded
    change source24206.get? (0 + index) = destination24206_0.get? index
    have same : source24206 = destination24206_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24206 : (target24206.map Setup.Block.length).sum = source24206.length := by decide +kernel

noncomputable def source24207 : Setup.Block := original.get ⟨15, by decide +kernel⟩

column_blocks_part part24207_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24207 stop 24208
noncomputable def destination24207_0 : Setup.Block := part24207_0.get ⟨0, by decide +kernel⟩

noncomputable def target24207 : List Setup.Block := part24207_0

theorem follows24207 : blockTargetsFollow source24207 0 target24207 :=
  And.intro (by
    intro index bounded
    change source24207.get? (0 + index) = destination24207_0.get? index
    have same : source24207 = destination24207_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24207 : (target24207.map Setup.Block.length).sum = source24207.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
