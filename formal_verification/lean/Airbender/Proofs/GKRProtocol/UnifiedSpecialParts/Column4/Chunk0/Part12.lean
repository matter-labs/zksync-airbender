import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source96 : Setup.Block := original.get ⟨96, by decide +kernel⟩

column_blocks_part part96_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 96 stop 97
noncomputable def destination96_0 : Setup.Block := part96_0.get ⟨0, by decide +kernel⟩

noncomputable def target96 : List Setup.Block := part96_0

theorem follows96 : blockTargetsFollow source96 0 target96 :=
  And.intro (by
    intro index bounded
    change source96.get? (0 + index) = destination96_0.get? index
    have same : source96 = destination96_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length96 : (target96.map Setup.Block.length).sum = source96.length := by decide +kernel

noncomputable def source97 : Setup.Block := original.get ⟨97, by decide +kernel⟩

column_blocks_part part97_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 97 stop 98
noncomputable def destination97_0 : Setup.Block := part97_0.get ⟨0, by decide +kernel⟩

noncomputable def target97 : List Setup.Block := part97_0

theorem follows97 : blockTargetsFollow source97 0 target97 :=
  And.intro (by
    intro index bounded
    change source97.get? (0 + index) = destination97_0.get? index
    have same : source97 = destination97_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length97 : (target97.map Setup.Block.length).sum = source97.length := by decide +kernel

noncomputable def source98 : Setup.Block := original.get ⟨98, by decide +kernel⟩

column_blocks_part part98_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 98 stop 99
noncomputable def destination98_0 : Setup.Block := part98_0.get ⟨0, by decide +kernel⟩

noncomputable def target98 : List Setup.Block := part98_0

theorem follows98 : blockTargetsFollow source98 0 target98 :=
  And.intro (by
    intro index bounded
    change source98.get? (0 + index) = destination98_0.get? index
    have same : source98 = destination98_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length98 : (target98.map Setup.Block.length).sum = source98.length := by decide +kernel

noncomputable def source99 : Setup.Block := original.get ⟨99, by decide +kernel⟩

column_blocks_part part99_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 99 stop 100
noncomputable def destination99_0 : Setup.Block := part99_0.get ⟨0, by decide +kernel⟩

noncomputable def target99 : List Setup.Block := part99_0

theorem follows99 : blockTargetsFollow source99 0 target99 :=
  And.intro (by
    intro index bounded
    change source99.get? (0 + index) = destination99_0.get? index
    have same : source99 = destination99_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length99 : (target99.map Setup.Block.length).sum = source99.length := by decide +kernel

noncomputable def source100 : Setup.Block := original.get ⟨100, by decide +kernel⟩

column_blocks_part part100_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 100 stop 101
noncomputable def destination100_0 : Setup.Block := part100_0.get ⟨0, by decide +kernel⟩

noncomputable def target100 : List Setup.Block := part100_0

theorem follows100 : blockTargetsFollow source100 0 target100 :=
  And.intro (by
    intro index bounded
    change source100.get? (0 + index) = destination100_0.get? index
    have same : source100 = destination100_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length100 : (target100.map Setup.Block.length).sum = source100.length := by decide +kernel

noncomputable def source101 : Setup.Block := original.get ⟨101, by decide +kernel⟩

column_blocks_part part101_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 101 stop 102
noncomputable def destination101_0 : Setup.Block := part101_0.get ⟨0, by decide +kernel⟩

noncomputable def target101 : List Setup.Block := part101_0

theorem follows101 : blockTargetsFollow source101 0 target101 :=
  And.intro (by
    intro index bounded
    change source101.get? (0 + index) = destination101_0.get? index
    have same : source101 = destination101_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length101 : (target101.map Setup.Block.length).sum = source101.length := by decide +kernel

noncomputable def source102 : Setup.Block := original.get ⟨102, by decide +kernel⟩

column_blocks_part part102_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 102 stop 103
noncomputable def destination102_0 : Setup.Block := part102_0.get ⟨0, by decide +kernel⟩

noncomputable def target102 : List Setup.Block := part102_0

theorem follows102 : blockTargetsFollow source102 0 target102 :=
  And.intro (by
    intro index bounded
    change source102.get? (0 + index) = destination102_0.get? index
    have same : source102 = destination102_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length102 : (target102.map Setup.Block.length).sum = source102.length := by decide +kernel

noncomputable def source103 : Setup.Block := original.get ⟨103, by decide +kernel⟩

column_blocks_part part103_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 103 stop 104
noncomputable def destination103_0 : Setup.Block := part103_0.get ⟨0, by decide +kernel⟩

noncomputable def target103 : List Setup.Block := part103_0

theorem follows103 : blockTargetsFollow source103 0 target103 :=
  And.intro (by
    intro index bounded
    change source103.get? (0 + index) = destination103_0.get? index
    have same : source103 = destination103_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length103 : (target103.map Setup.Block.length).sum = source103.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
