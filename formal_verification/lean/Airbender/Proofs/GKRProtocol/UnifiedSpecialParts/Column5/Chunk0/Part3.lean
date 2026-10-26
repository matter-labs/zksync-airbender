import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24 : Setup.Block := original.get ⟨24, by decide +kernel⟩

column_blocks_part part24_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24 stop 25
noncomputable def destination24_0 : Setup.Block := part24_0.get ⟨0, by decide +kernel⟩

noncomputable def target24 : List Setup.Block := part24_0

theorem follows24 : blockTargetsFollow source24 0 target24 :=
  And.intro (by
    intro index bounded
    change source24.get? (0 + index) = destination24_0.get? index
    have same : source24 = destination24_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24 : (target24.map Setup.Block.length).sum = source24.length := by decide +kernel

noncomputable def source25 : Setup.Block := original.get ⟨25, by decide +kernel⟩

column_blocks_part part25_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 25 stop 26
noncomputable def destination25_0 : Setup.Block := part25_0.get ⟨0, by decide +kernel⟩

noncomputable def target25 : List Setup.Block := part25_0

theorem follows25 : blockTargetsFollow source25 0 target25 :=
  And.intro (by
    intro index bounded
    change source25.get? (0 + index) = destination25_0.get? index
    have same : source25 = destination25_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25 : (target25.map Setup.Block.length).sum = source25.length := by decide +kernel

noncomputable def source26 : Setup.Block := original.get ⟨26, by decide +kernel⟩

column_blocks_part part26_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 26 stop 27
noncomputable def destination26_0 : Setup.Block := part26_0.get ⟨0, by decide +kernel⟩

noncomputable def target26 : List Setup.Block := part26_0

theorem follows26 : blockTargetsFollow source26 0 target26 :=
  And.intro (by
    intro index bounded
    change source26.get? (0 + index) = destination26_0.get? index
    have same : source26 = destination26_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26 : (target26.map Setup.Block.length).sum = source26.length := by decide +kernel

noncomputable def source27 : Setup.Block := original.get ⟨27, by decide +kernel⟩

column_blocks_part part27_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 27 stop 28
noncomputable def destination27_0 : Setup.Block := part27_0.get ⟨0, by decide +kernel⟩

noncomputable def target27 : List Setup.Block := part27_0

theorem follows27 : blockTargetsFollow source27 0 target27 :=
  And.intro (by
    intro index bounded
    change source27.get? (0 + index) = destination27_0.get? index
    have same : source27 = destination27_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length27 : (target27.map Setup.Block.length).sum = source27.length := by decide +kernel

noncomputable def source28 : Setup.Block := original.get ⟨28, by decide +kernel⟩

column_blocks_part part28_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 28 stop 29
noncomputable def destination28_0 : Setup.Block := part28_0.get ⟨0, by decide +kernel⟩

noncomputable def target28 : List Setup.Block := part28_0

theorem follows28 : blockTargetsFollow source28 0 target28 :=
  And.intro (by
    intro index bounded
    change source28.get? (0 + index) = destination28_0.get? index
    have same : source28 = destination28_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length28 : (target28.map Setup.Block.length).sum = source28.length := by decide +kernel

noncomputable def source29 : Setup.Block := original.get ⟨29, by decide +kernel⟩

column_blocks_part part29_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 29 stop 30
noncomputable def destination29_0 : Setup.Block := part29_0.get ⟨0, by decide +kernel⟩

noncomputable def target29 : List Setup.Block := part29_0

theorem follows29 : blockTargetsFollow source29 0 target29 :=
  And.intro (by
    intro index bounded
    change source29.get? (0 + index) = destination29_0.get? index
    have same : source29 = destination29_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length29 : (target29.map Setup.Block.length).sum = source29.length := by decide +kernel

noncomputable def source30 : Setup.Block := original.get ⟨30, by decide +kernel⟩

column_blocks_part part30_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 30 stop 31
noncomputable def destination30_0 : Setup.Block := part30_0.get ⟨0, by decide +kernel⟩

noncomputable def target30 : List Setup.Block := part30_0

theorem follows30 : blockTargetsFollow source30 0 target30 :=
  And.intro (by
    intro index bounded
    change source30.get? (0 + index) = destination30_0.get? index
    have same : source30 = destination30_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length30 : (target30.map Setup.Block.length).sum = source30.length := by decide +kernel

noncomputable def source31 : Setup.Block := original.get ⟨31, by decide +kernel⟩

column_blocks_part part31_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 31 stop 32
noncomputable def destination31_0 : Setup.Block := part31_0.get ⟨0, by decide +kernel⟩

noncomputable def target31 : List Setup.Block := part31_0

theorem follows31 : blockTargetsFollow source31 0 target31 :=
  And.intro (by
    intro index bounded
    change source31.get? (0 + index) = destination31_0.get? index
    have same : source31 = destination31_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length31 : (target31.map Setup.Block.length).sum = source31.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk0
