import GKRProtocol.UnifiedSpecialParts.Column7.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source80 : Setup.Block := original.get ⟨80, by decide +kernel⟩

column_blocks_part part80_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 80 stop 81
noncomputable def destination80_0 : Setup.Block := part80_0.get ⟨0, by decide +kernel⟩

noncomputable def target80 : List Setup.Block := part80_0

theorem follows80 : blockTargetsFollow source80 0 target80 :=
  And.intro (by
    intro index bounded
    change source80.get? (0 + index) = destination80_0.get? index
    have same : source80 = destination80_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length80 : (target80.map Setup.Block.length).sum = source80.length := by decide +kernel

noncomputable def source81 : Setup.Block := original.get ⟨81, by decide +kernel⟩

column_blocks_part part81_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 81 stop 82
noncomputable def destination81_0 : Setup.Block := part81_0.get ⟨0, by decide +kernel⟩

noncomputable def target81 : List Setup.Block := part81_0

theorem follows81 : blockTargetsFollow source81 0 target81 :=
  And.intro (by
    intro index bounded
    change source81.get? (0 + index) = destination81_0.get? index
    have same : source81 = destination81_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length81 : (target81.map Setup.Block.length).sum = source81.length := by decide +kernel

noncomputable def source82 : Setup.Block := original.get ⟨82, by decide +kernel⟩

column_blocks_part part82_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 82 stop 83
noncomputable def destination82_0 : Setup.Block := part82_0.get ⟨0, by decide +kernel⟩

noncomputable def target82 : List Setup.Block := part82_0

theorem follows82 : blockTargetsFollow source82 0 target82 :=
  And.intro (by
    intro index bounded
    change source82.get? (0 + index) = destination82_0.get? index
    have same : source82 = destination82_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length82 : (target82.map Setup.Block.length).sum = source82.length := by decide +kernel

noncomputable def source83 : Setup.Block := original.get ⟨83, by decide +kernel⟩

column_blocks_part part83_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 83 stop 84
noncomputable def destination83_0 : Setup.Block := part83_0.get ⟨0, by decide +kernel⟩

noncomputable def target83 : List Setup.Block := part83_0

theorem follows83 : blockTargetsFollow source83 0 target83 :=
  And.intro (by
    intro index bounded
    change source83.get? (0 + index) = destination83_0.get? index
    have same : source83 = destination83_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length83 : (target83.map Setup.Block.length).sum = source83.length := by decide +kernel

noncomputable def source84 : Setup.Block := original.get ⟨84, by decide +kernel⟩

column_blocks_part part84_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 84 stop 85
noncomputable def destination84_0 : Setup.Block := part84_0.get ⟨0, by decide +kernel⟩

noncomputable def target84 : List Setup.Block := part84_0

theorem follows84 : blockTargetsFollow source84 0 target84 :=
  And.intro (by
    intro index bounded
    change source84.get? (0 + index) = destination84_0.get? index
    have same : source84 = destination84_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length84 : (target84.map Setup.Block.length).sum = source84.length := by decide +kernel

noncomputable def source85 : Setup.Block := original.get ⟨85, by decide +kernel⟩

column_blocks_part part85_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 85 stop 86
noncomputable def destination85_0 : Setup.Block := part85_0.get ⟨0, by decide +kernel⟩

noncomputable def target85 : List Setup.Block := part85_0

theorem follows85 : blockTargetsFollow source85 0 target85 :=
  And.intro (by
    intro index bounded
    change source85.get? (0 + index) = destination85_0.get? index
    have same : source85 = destination85_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length85 : (target85.map Setup.Block.length).sum = source85.length := by decide +kernel

noncomputable def source86 : Setup.Block := original.get ⟨86, by decide +kernel⟩

column_blocks_part part86_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 86 stop 87
noncomputable def destination86_0 : Setup.Block := part86_0.get ⟨0, by decide +kernel⟩

noncomputable def target86 : List Setup.Block := part86_0

theorem follows86 : blockTargetsFollow source86 0 target86 :=
  And.intro (by
    intro index bounded
    change source86.get? (0 + index) = destination86_0.get? index
    have same : source86 = destination86_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length86 : (target86.map Setup.Block.length).sum = source86.length := by decide +kernel

noncomputable def source87 : Setup.Block := original.get ⟨87, by decide +kernel⟩

column_blocks_part part87_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 87 stop 88
noncomputable def destination87_0 : Setup.Block := part87_0.get ⟨0, by decide +kernel⟩

noncomputable def target87 : List Setup.Block := part87_0

theorem follows87 : blockTargetsFollow source87 0 target87 :=
  And.intro (by
    intro index bounded
    change source87.get? (0 + index) = destination87_0.get? index
    have same : source87 = destination87_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length87 : (target87.map Setup.Block.length).sum = source87.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk0
