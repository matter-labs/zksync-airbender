import GKRProtocol.UnifiedSpecialParts.Column4.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source16 : Setup.Block := original.get ⟨16, by decide +kernel⟩

column_blocks_part part16_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 16 stop 17
noncomputable def destination16_0 : Setup.Block := part16_0.get ⟨0, by decide +kernel⟩

noncomputable def target16 : List Setup.Block := part16_0

theorem follows16 : blockTargetsFollow source16 0 target16 :=
  And.intro (by
    intro index bounded
    change source16.get? (0 + index) = destination16_0.get? index
    have same : source16 = destination16_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length16 : (target16.map Setup.Block.length).sum = source16.length := by decide +kernel

noncomputable def source17 : Setup.Block := original.get ⟨17, by decide +kernel⟩

column_blocks_part part17_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 17 stop 18
noncomputable def destination17_0 : Setup.Block := part17_0.get ⟨0, by decide +kernel⟩

noncomputable def target17 : List Setup.Block := part17_0

theorem follows17 : blockTargetsFollow source17 0 target17 :=
  And.intro (by
    intro index bounded
    change source17.get? (0 + index) = destination17_0.get? index
    have same : source17 = destination17_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length17 : (target17.map Setup.Block.length).sum = source17.length := by decide +kernel

noncomputable def source18 : Setup.Block := original.get ⟨18, by decide +kernel⟩

column_blocks_part part18_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 18 stop 19
noncomputable def destination18_0 : Setup.Block := part18_0.get ⟨0, by decide +kernel⟩

noncomputable def target18 : List Setup.Block := part18_0

theorem follows18 : blockTargetsFollow source18 0 target18 :=
  And.intro (by
    intro index bounded
    change source18.get? (0 + index) = destination18_0.get? index
    have same : source18 = destination18_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length18 : (target18.map Setup.Block.length).sum = source18.length := by decide +kernel

noncomputable def source19 : Setup.Block := original.get ⟨19, by decide +kernel⟩

column_blocks_part part19_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 19 stop 20
noncomputable def destination19_0 : Setup.Block := part19_0.get ⟨0, by decide +kernel⟩

noncomputable def target19 : List Setup.Block := part19_0

theorem follows19 : blockTargetsFollow source19 0 target19 :=
  And.intro (by
    intro index bounded
    change source19.get? (0 + index) = destination19_0.get? index
    have same : source19 = destination19_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length19 : (target19.map Setup.Block.length).sum = source19.length := by decide +kernel

noncomputable def source20 : Setup.Block := original.get ⟨20, by decide +kernel⟩

column_blocks_part part20_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 20 stop 21
noncomputable def destination20_0 : Setup.Block := part20_0.get ⟨0, by decide +kernel⟩

noncomputable def target20 : List Setup.Block := part20_0

theorem follows20 : blockTargetsFollow source20 0 target20 :=
  And.intro (by
    intro index bounded
    change source20.get? (0 + index) = destination20_0.get? index
    have same : source20 = destination20_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length20 : (target20.map Setup.Block.length).sum = source20.length := by decide +kernel

noncomputable def source21 : Setup.Block := original.get ⟨21, by decide +kernel⟩

column_blocks_part part21_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 21 stop 22
noncomputable def destination21_0 : Setup.Block := part21_0.get ⟨0, by decide +kernel⟩

noncomputable def target21 : List Setup.Block := part21_0

theorem follows21 : blockTargetsFollow source21 0 target21 :=
  And.intro (by
    intro index bounded
    change source21.get? (0 + index) = destination21_0.get? index
    have same : source21 = destination21_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length21 : (target21.map Setup.Block.length).sum = source21.length := by decide +kernel

noncomputable def source22 : Setup.Block := original.get ⟨22, by decide +kernel⟩

column_blocks_part part22_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 22 stop 23
noncomputable def destination22_0 : Setup.Block := part22_0.get ⟨0, by decide +kernel⟩

noncomputable def target22 : List Setup.Block := part22_0

theorem follows22 : blockTargetsFollow source22 0 target22 :=
  And.intro (by
    intro index bounded
    change source22.get? (0 + index) = destination22_0.get? index
    have same : source22 = destination22_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length22 : (target22.map Setup.Block.length).sum = source22.length := by decide +kernel

noncomputable def source23 : Setup.Block := original.get ⟨23, by decide +kernel⟩

column_blocks_part part23_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 23 stop 24
noncomputable def destination23_0 : Setup.Block := part23_0.get ⟨0, by decide +kernel⟩

noncomputable def target23 : List Setup.Block := part23_0

theorem follows23 : blockTargetsFollow source23 0 target23 :=
  And.intro (by
    intro index bounded
    change source23.get? (0 + index) = destination23_0.get? index
    have same : source23 = destination23_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length23 : (target23.map Setup.Block.length).sum = source23.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
