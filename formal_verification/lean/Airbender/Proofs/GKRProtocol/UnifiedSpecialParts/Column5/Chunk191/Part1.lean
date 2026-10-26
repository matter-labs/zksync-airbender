import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24456 : Setup.Block := original.get ⟨8, by decide +kernel⟩

column_blocks_part part24456_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24456 stop 24457
noncomputable def destination24456_0 : Setup.Block := part24456_0.get ⟨0, by decide +kernel⟩

noncomputable def target24456 : List Setup.Block := part24456_0

theorem follows24456 : blockTargetsFollow source24456 0 target24456 :=
  And.intro (by
    intro index bounded
    change source24456.get? (0 + index) = destination24456_0.get? index
    have same : source24456 = destination24456_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24456 : (target24456.map Setup.Block.length).sum = source24456.length := by decide +kernel

noncomputable def source24457 : Setup.Block := original.get ⟨9, by decide +kernel⟩

column_blocks_part part24457_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24457 stop 24458
noncomputable def destination24457_0 : Setup.Block := part24457_0.get ⟨0, by decide +kernel⟩

noncomputable def target24457 : List Setup.Block := part24457_0

theorem follows24457 : blockTargetsFollow source24457 0 target24457 :=
  And.intro (by
    intro index bounded
    change source24457.get? (0 + index) = destination24457_0.get? index
    have same : source24457 = destination24457_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24457 : (target24457.map Setup.Block.length).sum = source24457.length := by decide +kernel

noncomputable def source24458 : Setup.Block := original.get ⟨10, by decide +kernel⟩

column_blocks_part part24458_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24458 stop 24459
noncomputable def destination24458_0 : Setup.Block := part24458_0.get ⟨0, by decide +kernel⟩

noncomputable def target24458 : List Setup.Block := part24458_0

theorem follows24458 : blockTargetsFollow source24458 0 target24458 :=
  And.intro (by
    intro index bounded
    change source24458.get? (0 + index) = destination24458_0.get? index
    have same : source24458 = destination24458_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24458 : (target24458.map Setup.Block.length).sum = source24458.length := by decide +kernel

noncomputable def source24459 : Setup.Block := original.get ⟨11, by decide +kernel⟩

column_blocks_part part24459_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24459 stop 24460
noncomputable def destination24459_0 : Setup.Block := part24459_0.get ⟨0, by decide +kernel⟩

noncomputable def target24459 : List Setup.Block := part24459_0

theorem follows24459 : blockTargetsFollow source24459 0 target24459 :=
  And.intro (by
    intro index bounded
    change source24459.get? (0 + index) = destination24459_0.get? index
    have same : source24459 = destination24459_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24459 : (target24459.map Setup.Block.length).sum = source24459.length := by decide +kernel

noncomputable def source24460 : Setup.Block := original.get ⟨12, by decide +kernel⟩

column_blocks_part part24460_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24460 stop 24461
noncomputable def destination24460_0 : Setup.Block := part24460_0.get ⟨0, by decide +kernel⟩

noncomputable def target24460 : List Setup.Block := part24460_0

theorem follows24460 : blockTargetsFollow source24460 0 target24460 :=
  And.intro (by
    intro index bounded
    change source24460.get? (0 + index) = destination24460_0.get? index
    have same : source24460 = destination24460_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24460 : (target24460.map Setup.Block.length).sum = source24460.length := by decide +kernel

noncomputable def source24461 : Setup.Block := original.get ⟨13, by decide +kernel⟩

column_blocks_part part24461_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24461 stop 24462
noncomputable def destination24461_0 : Setup.Block := part24461_0.get ⟨0, by decide +kernel⟩

noncomputable def target24461 : List Setup.Block := part24461_0

theorem follows24461 : blockTargetsFollow source24461 0 target24461 :=
  And.intro (by
    intro index bounded
    change source24461.get? (0 + index) = destination24461_0.get? index
    have same : source24461 = destination24461_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24461 : (target24461.map Setup.Block.length).sum = source24461.length := by decide +kernel

noncomputable def source24462 : Setup.Block := original.get ⟨14, by decide +kernel⟩

column_blocks_part part24462_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24462 stop 24463
noncomputable def destination24462_0 : Setup.Block := part24462_0.get ⟨0, by decide +kernel⟩

noncomputable def target24462 : List Setup.Block := part24462_0

theorem follows24462 : blockTargetsFollow source24462 0 target24462 :=
  And.intro (by
    intro index bounded
    change source24462.get? (0 + index) = destination24462_0.get? index
    have same : source24462 = destination24462_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24462 : (target24462.map Setup.Block.length).sum = source24462.length := by decide +kernel

noncomputable def source24463 : Setup.Block := original.get ⟨15, by decide +kernel⟩

column_blocks_part part24463_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24463 stop 24464
noncomputable def destination24463_0 : Setup.Block := part24463_0.get ⟨0, by decide +kernel⟩

noncomputable def target24463 : List Setup.Block := part24463_0

theorem follows24463 : blockTargetsFollow source24463 0 target24463 :=
  And.intro (by
    intro index bounded
    change source24463.get? (0 + index) = destination24463_0.get? index
    have same : source24463 = destination24463_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24463 : (target24463.map Setup.Block.length).sum = source24463.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
