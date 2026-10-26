import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source120 : Setup.Block := original.get ⟨120, by decide +kernel⟩

column_blocks_part part120_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 120 stop 121
noncomputable def destination120_0 : Setup.Block := part120_0.get ⟨0, by decide +kernel⟩

noncomputable def target120 : List Setup.Block := part120_0

theorem follows120 : blockTargetsFollow source120 0 target120 :=
  And.intro (by
    intro index bounded
    change source120.get? (0 + index) = destination120_0.get? index
    have same : source120 = destination120_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length120 : (target120.map Setup.Block.length).sum = source120.length := by decide +kernel

noncomputable def source121 : Setup.Block := original.get ⟨121, by decide +kernel⟩

column_blocks_part part121_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 121 stop 122
noncomputable def destination121_0 : Setup.Block := part121_0.get ⟨0, by decide +kernel⟩

noncomputable def target121 : List Setup.Block := part121_0

theorem follows121 : blockTargetsFollow source121 0 target121 :=
  And.intro (by
    intro index bounded
    change source121.get? (0 + index) = destination121_0.get? index
    have same : source121 = destination121_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length121 : (target121.map Setup.Block.length).sum = source121.length := by decide +kernel

noncomputable def source122 : Setup.Block := original.get ⟨122, by decide +kernel⟩

column_blocks_part part122_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 122 stop 123
noncomputable def destination122_0 : Setup.Block := part122_0.get ⟨0, by decide +kernel⟩

noncomputable def target122 : List Setup.Block := part122_0

theorem follows122 : blockTargetsFollow source122 0 target122 :=
  And.intro (by
    intro index bounded
    change source122.get? (0 + index) = destination122_0.get? index
    have same : source122 = destination122_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length122 : (target122.map Setup.Block.length).sum = source122.length := by decide +kernel

noncomputable def source123 : Setup.Block := original.get ⟨123, by decide +kernel⟩

column_blocks_part part123_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 123 stop 124
noncomputable def destination123_0 : Setup.Block := part123_0.get ⟨0, by decide +kernel⟩

noncomputable def target123 : List Setup.Block := part123_0

theorem follows123 : blockTargetsFollow source123 0 target123 :=
  And.intro (by
    intro index bounded
    change source123.get? (0 + index) = destination123_0.get? index
    have same : source123 = destination123_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length123 : (target123.map Setup.Block.length).sum = source123.length := by decide +kernel

noncomputable def source124 : Setup.Block := original.get ⟨124, by decide +kernel⟩

column_blocks_part part124_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 124 stop 125
noncomputable def destination124_0 : Setup.Block := part124_0.get ⟨0, by decide +kernel⟩

noncomputable def target124 : List Setup.Block := part124_0

theorem follows124 : blockTargetsFollow source124 0 target124 :=
  And.intro (by
    intro index bounded
    change source124.get? (0 + index) = destination124_0.get? index
    have same : source124 = destination124_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length124 : (target124.map Setup.Block.length).sum = source124.length := by decide +kernel

noncomputable def source125 : Setup.Block := original.get ⟨125, by decide +kernel⟩

column_blocks_part part125_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 125 stop 126
noncomputable def destination125_0 : Setup.Block := part125_0.get ⟨0, by decide +kernel⟩

noncomputable def target125 : List Setup.Block := part125_0

theorem follows125 : blockTargetsFollow source125 0 target125 :=
  And.intro (by
    intro index bounded
    change source125.get? (0 + index) = destination125_0.get? index
    have same : source125 = destination125_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length125 : (target125.map Setup.Block.length).sum = source125.length := by decide +kernel

noncomputable def source126 : Setup.Block := original.get ⟨126, by decide +kernel⟩

column_blocks_part part126_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 126 stop 127
noncomputable def destination126_0 : Setup.Block := part126_0.get ⟨0, by decide +kernel⟩

noncomputable def target126 : List Setup.Block := part126_0

theorem follows126 : blockTargetsFollow source126 0 target126 :=
  And.intro (by
    intro index bounded
    change source126.get? (0 + index) = destination126_0.get? index
    have same : source126 = destination126_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length126 : (target126.map Setup.Block.length).sum = source126.length := by decide +kernel

noncomputable def source127 : Setup.Block := original.get ⟨127, by decide +kernel⟩

column_blocks_part part127_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 127 stop 128
noncomputable def destination127_0 : Setup.Block := part127_0.get ⟨0, by decide +kernel⟩

noncomputable def target127 : List Setup.Block := part127_0

theorem follows127 : blockTargetsFollow source127 0 target127 :=
  And.intro (by
    intro index bounded
    change source127.get? (0 + index) = destination127_0.get? index
    have same : source127 = destination127_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length127 : (target127.map Setup.Block.length).sum = source127.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
