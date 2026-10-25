import GKRProtocol.UnifiedSpecialParts.Column4.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source104 : Setup.Block := original.get ⟨104, by decide +kernel⟩

column_blocks_part part104_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 104 stop 105
noncomputable def destination104_0 : Setup.Block := part104_0.get ⟨0, by decide +kernel⟩

noncomputable def target104 : List Setup.Block := part104_0

theorem follows104 : blockTargetsFollow source104 0 target104 :=
  And.intro (by
    intro index bounded
    change source104.get? (0 + index) = destination104_0.get? index
    have same : source104 = destination104_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length104 : (target104.map Setup.Block.length).sum = source104.length := by decide +kernel

noncomputable def source105 : Setup.Block := original.get ⟨105, by decide +kernel⟩

column_blocks_part part105_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 105 stop 106
noncomputable def destination105_0 : Setup.Block := part105_0.get ⟨0, by decide +kernel⟩

noncomputable def target105 : List Setup.Block := part105_0

theorem follows105 : blockTargetsFollow source105 0 target105 :=
  And.intro (by
    intro index bounded
    change source105.get? (0 + index) = destination105_0.get? index
    have same : source105 = destination105_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length105 : (target105.map Setup.Block.length).sum = source105.length := by decide +kernel

noncomputable def source106 : Setup.Block := original.get ⟨106, by decide +kernel⟩

column_blocks_part part106_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 106 stop 107
noncomputable def destination106_0 : Setup.Block := part106_0.get ⟨0, by decide +kernel⟩

noncomputable def target106 : List Setup.Block := part106_0

theorem follows106 : blockTargetsFollow source106 0 target106 :=
  And.intro (by
    intro index bounded
    change source106.get? (0 + index) = destination106_0.get? index
    have same : source106 = destination106_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length106 : (target106.map Setup.Block.length).sum = source106.length := by decide +kernel

noncomputable def source107 : Setup.Block := original.get ⟨107, by decide +kernel⟩

column_blocks_part part107_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 107 stop 108
noncomputable def destination107_0 : Setup.Block := part107_0.get ⟨0, by decide +kernel⟩

noncomputable def target107 : List Setup.Block := part107_0

theorem follows107 : blockTargetsFollow source107 0 target107 :=
  And.intro (by
    intro index bounded
    change source107.get? (0 + index) = destination107_0.get? index
    have same : source107 = destination107_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length107 : (target107.map Setup.Block.length).sum = source107.length := by decide +kernel

noncomputable def source108 : Setup.Block := original.get ⟨108, by decide +kernel⟩

column_blocks_part part108_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 108 stop 109
noncomputable def destination108_0 : Setup.Block := part108_0.get ⟨0, by decide +kernel⟩

noncomputable def target108 : List Setup.Block := part108_0

theorem follows108 : blockTargetsFollow source108 0 target108 :=
  And.intro (by
    intro index bounded
    change source108.get? (0 + index) = destination108_0.get? index
    have same : source108 = destination108_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length108 : (target108.map Setup.Block.length).sum = source108.length := by decide +kernel

noncomputable def source109 : Setup.Block := original.get ⟨109, by decide +kernel⟩

column_blocks_part part109_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 109 stop 110
noncomputable def destination109_0 : Setup.Block := part109_0.get ⟨0, by decide +kernel⟩

noncomputable def target109 : List Setup.Block := part109_0

theorem follows109 : blockTargetsFollow source109 0 target109 :=
  And.intro (by
    intro index bounded
    change source109.get? (0 + index) = destination109_0.get? index
    have same : source109 = destination109_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length109 : (target109.map Setup.Block.length).sum = source109.length := by decide +kernel

noncomputable def source110 : Setup.Block := original.get ⟨110, by decide +kernel⟩

column_blocks_part part110_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 110 stop 111
noncomputable def destination110_0 : Setup.Block := part110_0.get ⟨0, by decide +kernel⟩

noncomputable def target110 : List Setup.Block := part110_0

theorem follows110 : blockTargetsFollow source110 0 target110 :=
  And.intro (by
    intro index bounded
    change source110.get? (0 + index) = destination110_0.get? index
    have same : source110 = destination110_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length110 : (target110.map Setup.Block.length).sum = source110.length := by decide +kernel

noncomputable def source111 : Setup.Block := original.get ⟨111, by decide +kernel⟩

column_blocks_part part111_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 111 stop 112
noncomputable def destination111_0 : Setup.Block := part111_0.get ⟨0, by decide +kernel⟩

noncomputable def target111 : List Setup.Block := part111_0

theorem follows111 : blockTargetsFollow source111 0 target111 :=
  And.intro (by
    intro index bounded
    change source111.get? (0 + index) = destination111_0.get? index
    have same : source111 = destination111_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length111 : (target111.map Setup.Block.length).sum = source111.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
