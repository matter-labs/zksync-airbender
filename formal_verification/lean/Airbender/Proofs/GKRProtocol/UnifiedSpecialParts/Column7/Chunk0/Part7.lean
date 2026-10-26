import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column7.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source56 : Setup.Block := original.get ⟨56, by decide +kernel⟩

column_blocks_part part56_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 56 stop 57
noncomputable def destination56_0 : Setup.Block := part56_0.get ⟨0, by decide +kernel⟩

noncomputable def target56 : List Setup.Block := part56_0

theorem follows56 : blockTargetsFollow source56 0 target56 :=
  And.intro (by
    intro index bounded
    change source56.get? (0 + index) = destination56_0.get? index
    have same : source56 = destination56_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length56 : (target56.map Setup.Block.length).sum = source56.length := by decide +kernel

noncomputable def source57 : Setup.Block := original.get ⟨57, by decide +kernel⟩

column_blocks_part part57_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 57 stop 58
noncomputable def destination57_0 : Setup.Block := part57_0.get ⟨0, by decide +kernel⟩

noncomputable def target57 : List Setup.Block := part57_0

theorem follows57 : blockTargetsFollow source57 0 target57 :=
  And.intro (by
    intro index bounded
    change source57.get? (0 + index) = destination57_0.get? index
    have same : source57 = destination57_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length57 : (target57.map Setup.Block.length).sum = source57.length := by decide +kernel

noncomputable def source58 : Setup.Block := original.get ⟨58, by decide +kernel⟩

column_blocks_part part58_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 58 stop 59
noncomputable def destination58_0 : Setup.Block := part58_0.get ⟨0, by decide +kernel⟩

noncomputable def target58 : List Setup.Block := part58_0

theorem follows58 : blockTargetsFollow source58 0 target58 :=
  And.intro (by
    intro index bounded
    change source58.get? (0 + index) = destination58_0.get? index
    have same : source58 = destination58_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length58 : (target58.map Setup.Block.length).sum = source58.length := by decide +kernel

noncomputable def source59 : Setup.Block := original.get ⟨59, by decide +kernel⟩

column_blocks_part part59_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 59 stop 60
noncomputable def destination59_0 : Setup.Block := part59_0.get ⟨0, by decide +kernel⟩

noncomputable def target59 : List Setup.Block := part59_0

theorem follows59 : blockTargetsFollow source59 0 target59 :=
  And.intro (by
    intro index bounded
    change source59.get? (0 + index) = destination59_0.get? index
    have same : source59 = destination59_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length59 : (target59.map Setup.Block.length).sum = source59.length := by decide +kernel

noncomputable def source60 : Setup.Block := original.get ⟨60, by decide +kernel⟩

column_blocks_part part60_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 60 stop 61
noncomputable def destination60_0 : Setup.Block := part60_0.get ⟨0, by decide +kernel⟩

noncomputable def target60 : List Setup.Block := part60_0

theorem follows60 : blockTargetsFollow source60 0 target60 :=
  And.intro (by
    intro index bounded
    change source60.get? (0 + index) = destination60_0.get? index
    have same : source60 = destination60_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length60 : (target60.map Setup.Block.length).sum = source60.length := by decide +kernel

noncomputable def source61 : Setup.Block := original.get ⟨61, by decide +kernel⟩

column_blocks_part part61_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 61 stop 62
noncomputable def destination61_0 : Setup.Block := part61_0.get ⟨0, by decide +kernel⟩

noncomputable def target61 : List Setup.Block := part61_0

theorem follows61 : blockTargetsFollow source61 0 target61 :=
  And.intro (by
    intro index bounded
    change source61.get? (0 + index) = destination61_0.get? index
    have same : source61 = destination61_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length61 : (target61.map Setup.Block.length).sum = source61.length := by decide +kernel

noncomputable def source62 : Setup.Block := original.get ⟨62, by decide +kernel⟩

column_blocks_part part62_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 62 stop 63
noncomputable def destination62_0 : Setup.Block := part62_0.get ⟨0, by decide +kernel⟩

noncomputable def target62 : List Setup.Block := part62_0

theorem follows62 : blockTargetsFollow source62 0 target62 :=
  And.intro (by
    intro index bounded
    change source62.get? (0 + index) = destination62_0.get? index
    have same : source62 = destination62_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length62 : (target62.map Setup.Block.length).sum = source62.length := by decide +kernel

noncomputable def source63 : Setup.Block := original.get ⟨63, by decide +kernel⟩

column_blocks_part part63_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 63 stop 64
noncomputable def destination63_0 : Setup.Block := part63_0.get ⟨0, by decide +kernel⟩

noncomputable def target63 : List Setup.Block := part63_0

theorem follows63 : blockTargetsFollow source63 0 target63 :=
  And.intro (by
    intro index bounded
    change source63.get? (0 + index) = destination63_0.get? index
    have same : source63 = destination63_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length63 : (target63.map Setup.Block.length).sum = source63.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk0
