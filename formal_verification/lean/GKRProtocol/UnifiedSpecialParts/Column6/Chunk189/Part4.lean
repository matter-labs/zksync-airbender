import GKRProtocol.UnifiedSpecialParts.Column6.Chunk189.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24224 : Setup.Block := original.get ⟨32, by decide +kernel⟩

column_blocks_part part24224_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24224 stop 24225
noncomputable def destination24224_0 : Setup.Block := part24224_0.get ⟨0, by decide +kernel⟩

noncomputable def target24224 : List Setup.Block := part24224_0

theorem follows24224 : blockTargetsFollow source24224 0 target24224 :=
  And.intro (by
    intro index bounded
    change source24224.get? (0 + index) = destination24224_0.get? index
    have same : source24224 = destination24224_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24224 : (target24224.map Setup.Block.length).sum = source24224.length := by decide +kernel

noncomputable def source24225 : Setup.Block := original.get ⟨33, by decide +kernel⟩

column_blocks_part part24225_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24225 stop 24226
noncomputable def destination24225_0 : Setup.Block := part24225_0.get ⟨0, by decide +kernel⟩

noncomputable def target24225 : List Setup.Block := part24225_0

theorem follows24225 : blockTargetsFollow source24225 0 target24225 :=
  And.intro (by
    intro index bounded
    change source24225.get? (0 + index) = destination24225_0.get? index
    have same : source24225 = destination24225_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24225 : (target24225.map Setup.Block.length).sum = source24225.length := by decide +kernel

noncomputable def source24226 : Setup.Block := original.get ⟨34, by decide +kernel⟩

column_blocks_part part24226_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24226 stop 24227
noncomputable def destination24226_0 : Setup.Block := part24226_0.get ⟨0, by decide +kernel⟩

noncomputable def target24226 : List Setup.Block := part24226_0

theorem follows24226 : blockTargetsFollow source24226 0 target24226 :=
  And.intro (by
    intro index bounded
    change source24226.get? (0 + index) = destination24226_0.get? index
    have same : source24226 = destination24226_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24226 : (target24226.map Setup.Block.length).sum = source24226.length := by decide +kernel

noncomputable def source24227 : Setup.Block := original.get ⟨35, by decide +kernel⟩

column_blocks_part part24227_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24227 stop 24228
noncomputable def destination24227_0 : Setup.Block := part24227_0.get ⟨0, by decide +kernel⟩

noncomputable def target24227 : List Setup.Block := part24227_0

theorem follows24227 : blockTargetsFollow source24227 0 target24227 :=
  And.intro (by
    intro index bounded
    change source24227.get? (0 + index) = destination24227_0.get? index
    have same : source24227 = destination24227_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24227 : (target24227.map Setup.Block.length).sum = source24227.length := by decide +kernel

noncomputable def source24228 : Setup.Block := original.get ⟨36, by decide +kernel⟩

column_blocks_part part24228_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24228 stop 24229
noncomputable def destination24228_0 : Setup.Block := part24228_0.get ⟨0, by decide +kernel⟩

noncomputable def target24228 : List Setup.Block := part24228_0

theorem follows24228 : blockTargetsFollow source24228 0 target24228 :=
  And.intro (by
    intro index bounded
    change source24228.get? (0 + index) = destination24228_0.get? index
    have same : source24228 = destination24228_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24228 : (target24228.map Setup.Block.length).sum = source24228.length := by decide +kernel

noncomputable def source24229 : Setup.Block := original.get ⟨37, by decide +kernel⟩

column_blocks_part part24229_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24229 stop 24230
noncomputable def destination24229_0 : Setup.Block := part24229_0.get ⟨0, by decide +kernel⟩

noncomputable def target24229 : List Setup.Block := part24229_0

theorem follows24229 : blockTargetsFollow source24229 0 target24229 :=
  And.intro (by
    intro index bounded
    change source24229.get? (0 + index) = destination24229_0.get? index
    have same : source24229 = destination24229_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24229 : (target24229.map Setup.Block.length).sum = source24229.length := by decide +kernel

noncomputable def source24230 : Setup.Block := original.get ⟨38, by decide +kernel⟩

column_blocks_part part24230_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24230 stop 24231
noncomputable def destination24230_0 : Setup.Block := part24230_0.get ⟨0, by decide +kernel⟩

noncomputable def target24230 : List Setup.Block := part24230_0

theorem follows24230 : blockTargetsFollow source24230 0 target24230 :=
  And.intro (by
    intro index bounded
    change source24230.get? (0 + index) = destination24230_0.get? index
    have same : source24230 = destination24230_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24230 : (target24230.map Setup.Block.length).sum = source24230.length := by decide +kernel

noncomputable def source24231 : Setup.Block := original.get ⟨39, by decide +kernel⟩

column_blocks_part part24231_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24231 stop 24232
noncomputable def destination24231_0 : Setup.Block := part24231_0.get ⟨0, by decide +kernel⟩

noncomputable def target24231 : List Setup.Block := part24231_0

theorem follows24231 : blockTargetsFollow source24231 0 target24231 :=
  And.intro (by
    intro index bounded
    change source24231.get? (0 + index) = destination24231_0.get? index
    have same : source24231 = destination24231_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24231 : (target24231.map Setup.Block.length).sum = source24231.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
