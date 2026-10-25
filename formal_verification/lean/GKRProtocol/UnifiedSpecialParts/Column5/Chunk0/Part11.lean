import GKRProtocol.UnifiedSpecialParts.Column5.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source88 : Setup.Block := original.get ⟨88, by decide +kernel⟩

column_blocks_part part88_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 88 stop 89
noncomputable def destination88_0 : Setup.Block := part88_0.get ⟨0, by decide +kernel⟩

noncomputable def target88 : List Setup.Block := part88_0

theorem follows88 : blockTargetsFollow source88 0 target88 :=
  And.intro (by
    intro index bounded
    change source88.get? (0 + index) = destination88_0.get? index
    have same : source88 = destination88_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length88 : (target88.map Setup.Block.length).sum = source88.length := by decide +kernel

noncomputable def source89 : Setup.Block := original.get ⟨89, by decide +kernel⟩

column_blocks_part part89_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 89 stop 90
noncomputable def destination89_0 : Setup.Block := part89_0.get ⟨0, by decide +kernel⟩

noncomputable def target89 : List Setup.Block := part89_0

theorem follows89 : blockTargetsFollow source89 0 target89 :=
  And.intro (by
    intro index bounded
    change source89.get? (0 + index) = destination89_0.get? index
    have same : source89 = destination89_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length89 : (target89.map Setup.Block.length).sum = source89.length := by decide +kernel

noncomputable def source90 : Setup.Block := original.get ⟨90, by decide +kernel⟩

column_blocks_part part90_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 90 stop 91
noncomputable def destination90_0 : Setup.Block := part90_0.get ⟨0, by decide +kernel⟩

noncomputable def target90 : List Setup.Block := part90_0

theorem follows90 : blockTargetsFollow source90 0 target90 :=
  And.intro (by
    intro index bounded
    change source90.get? (0 + index) = destination90_0.get? index
    have same : source90 = destination90_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length90 : (target90.map Setup.Block.length).sum = source90.length := by decide +kernel

noncomputable def source91 : Setup.Block := original.get ⟨91, by decide +kernel⟩

column_blocks_part part91_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 91 stop 92
noncomputable def destination91_0 : Setup.Block := part91_0.get ⟨0, by decide +kernel⟩

noncomputable def target91 : List Setup.Block := part91_0

theorem follows91 : blockTargetsFollow source91 0 target91 :=
  And.intro (by
    intro index bounded
    change source91.get? (0 + index) = destination91_0.get? index
    have same : source91 = destination91_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length91 : (target91.map Setup.Block.length).sum = source91.length := by decide +kernel

noncomputable def source92 : Setup.Block := original.get ⟨92, by decide +kernel⟩

column_blocks_part part92_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 92 stop 93
noncomputable def destination92_0 : Setup.Block := part92_0.get ⟨0, by decide +kernel⟩

noncomputable def target92 : List Setup.Block := part92_0

theorem follows92 : blockTargetsFollow source92 0 target92 :=
  And.intro (by
    intro index bounded
    change source92.get? (0 + index) = destination92_0.get? index
    have same : source92 = destination92_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length92 : (target92.map Setup.Block.length).sum = source92.length := by decide +kernel

noncomputable def source93 : Setup.Block := original.get ⟨93, by decide +kernel⟩

column_blocks_part part93_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 93 stop 94
noncomputable def destination93_0 : Setup.Block := part93_0.get ⟨0, by decide +kernel⟩

noncomputable def target93 : List Setup.Block := part93_0

theorem follows93 : blockTargetsFollow source93 0 target93 :=
  And.intro (by
    intro index bounded
    change source93.get? (0 + index) = destination93_0.get? index
    have same : source93 = destination93_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length93 : (target93.map Setup.Block.length).sum = source93.length := by decide +kernel

noncomputable def source94 : Setup.Block := original.get ⟨94, by decide +kernel⟩

column_blocks_part part94_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 94 stop 95
noncomputable def destination94_0 : Setup.Block := part94_0.get ⟨0, by decide +kernel⟩

noncomputable def target94 : List Setup.Block := part94_0

theorem follows94 : blockTargetsFollow source94 0 target94 :=
  And.intro (by
    intro index bounded
    change source94.get? (0 + index) = destination94_0.get? index
    have same : source94 = destination94_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length94 : (target94.map Setup.Block.length).sum = source94.length := by decide +kernel

noncomputable def source95 : Setup.Block := original.get ⟨95, by decide +kernel⟩

column_blocks_part part95_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 95 stop 96
noncomputable def destination95_0 : Setup.Block := part95_0.get ⟨0, by decide +kernel⟩

noncomputable def target95 : List Setup.Block := part95_0

theorem follows95 : blockTargetsFollow source95 0 target95 :=
  And.intro (by
    intro index bounded
    change source95.get? (0 + index) = destination95_0.get? index
    have same : source95 = destination95_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length95 : (target95.map Setup.Block.length).sum = source95.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
