import GKRProtocol.UnifiedSpecialParts.Column5.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source8 : Setup.Block := original.get ⟨8, by decide +kernel⟩

column_blocks_part part8_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 8 stop 9
noncomputable def destination8_0 : Setup.Block := part8_0.get ⟨0, by decide +kernel⟩

noncomputable def target8 : List Setup.Block := part8_0

theorem follows8 : blockTargetsFollow source8 0 target8 :=
  And.intro (by
    intro index bounded
    change source8.get? (0 + index) = destination8_0.get? index
    have same : source8 = destination8_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length8 : (target8.map Setup.Block.length).sum = source8.length := by decide +kernel

noncomputable def source9 : Setup.Block := original.get ⟨9, by decide +kernel⟩

column_blocks_part part9_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 9 stop 10
noncomputable def destination9_0 : Setup.Block := part9_0.get ⟨0, by decide +kernel⟩

noncomputable def target9 : List Setup.Block := part9_0

theorem follows9 : blockTargetsFollow source9 0 target9 :=
  And.intro (by
    intro index bounded
    change source9.get? (0 + index) = destination9_0.get? index
    have same : source9 = destination9_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length9 : (target9.map Setup.Block.length).sum = source9.length := by decide +kernel

noncomputable def source10 : Setup.Block := original.get ⟨10, by decide +kernel⟩

column_blocks_part part10_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 10 stop 11
noncomputable def destination10_0 : Setup.Block := part10_0.get ⟨0, by decide +kernel⟩

noncomputable def target10 : List Setup.Block := part10_0

theorem follows10 : blockTargetsFollow source10 0 target10 :=
  And.intro (by
    intro index bounded
    change source10.get? (0 + index) = destination10_0.get? index
    have same : source10 = destination10_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length10 : (target10.map Setup.Block.length).sum = source10.length := by decide +kernel

noncomputable def source11 : Setup.Block := original.get ⟨11, by decide +kernel⟩

column_blocks_part part11_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 11 stop 12
noncomputable def destination11_0 : Setup.Block := part11_0.get ⟨0, by decide +kernel⟩

noncomputable def target11 : List Setup.Block := part11_0

theorem follows11 : blockTargetsFollow source11 0 target11 :=
  And.intro (by
    intro index bounded
    change source11.get? (0 + index) = destination11_0.get? index
    have same : source11 = destination11_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length11 : (target11.map Setup.Block.length).sum = source11.length := by decide +kernel

noncomputable def source12 : Setup.Block := original.get ⟨12, by decide +kernel⟩

column_blocks_part part12_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 12 stop 13
noncomputable def destination12_0 : Setup.Block := part12_0.get ⟨0, by decide +kernel⟩

noncomputable def target12 : List Setup.Block := part12_0

theorem follows12 : blockTargetsFollow source12 0 target12 :=
  And.intro (by
    intro index bounded
    change source12.get? (0 + index) = destination12_0.get? index
    have same : source12 = destination12_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length12 : (target12.map Setup.Block.length).sum = source12.length := by decide +kernel

noncomputable def source13 : Setup.Block := original.get ⟨13, by decide +kernel⟩

column_blocks_part part13_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 13 stop 14
noncomputable def destination13_0 : Setup.Block := part13_0.get ⟨0, by decide +kernel⟩

noncomputable def target13 : List Setup.Block := part13_0

theorem follows13 : blockTargetsFollow source13 0 target13 :=
  And.intro (by
    intro index bounded
    change source13.get? (0 + index) = destination13_0.get? index
    have same : source13 = destination13_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length13 : (target13.map Setup.Block.length).sum = source13.length := by decide +kernel

noncomputable def source14 : Setup.Block := original.get ⟨14, by decide +kernel⟩

column_blocks_part part14_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 14 stop 15
noncomputable def destination14_0 : Setup.Block := part14_0.get ⟨0, by decide +kernel⟩

noncomputable def target14 : List Setup.Block := part14_0

set_option maxHeartbeats 16000000 in
theorem follows14 : blockTargetsFollow source14 0 target14 :=
  And.intro (by
    intro index bounded
    change source14.get? (0 + index) = destination14_0.get? index
    have same : source14 = destination14_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length14 : (target14.map Setup.Block.length).sum = source14.length := by decide +kernel

noncomputable def source15 : Setup.Block := original.get ⟨15, by decide +kernel⟩

column_blocks_part part15_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 15 stop 16
noncomputable def destination15_0 : Setup.Block := part15_0.get ⟨0, by decide +kernel⟩

noncomputable def target15 : List Setup.Block := part15_0

theorem follows15 : blockTargetsFollow source15 0 target15 :=
  And.intro (by
    intro index bounded
    change source15.get? (0 + index) = destination15_0.get? index
    have same : source15 = destination15_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length15 : (target15.map Setup.Block.length).sum = source15.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
