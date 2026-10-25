import GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source48 : Setup.Block := original.get ⟨48, by decide +kernel⟩

column_blocks_part part48_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 31 stop 32
noncomputable def destination48_0 : Setup.Block := part48_0.get ⟨0, by decide +kernel⟩

noncomputable def target48 : List Setup.Block := part48_0

theorem follows48 : blockTargetsFollow source48 0 target48 :=
  And.intro (by
    intro index bounded
    change source48.get? (0 + index) = destination48_0.get? index
    have same : source48 = destination48_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length48 : (target48.map Setup.Block.length).sum = source48.length := by decide +kernel

noncomputable def source49 : Setup.Block := original.get ⟨49, by decide +kernel⟩

column_blocks_part part49_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 32 stop 33
noncomputable def destination49_0 : Setup.Block := part49_0.get ⟨0, by decide +kernel⟩

noncomputable def target49 : List Setup.Block := part49_0

theorem follows49 : blockTargetsFollow source49 0 target49 :=
  And.intro (by
    intro index bounded
    change source49.get? (0 + index) = destination49_0.get? index
    have same : source49 = destination49_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length49 : (target49.map Setup.Block.length).sum = source49.length := by decide +kernel

noncomputable def source50 : Setup.Block := original.get ⟨50, by decide +kernel⟩

column_blocks_part part50_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 33 stop 34
noncomputable def destination50_0 : Setup.Block := part50_0.get ⟨0, by decide +kernel⟩

noncomputable def target50 : List Setup.Block := part50_0

theorem follows50 : blockTargetsFollow source50 0 target50 :=
  And.intro (by
    intro index bounded
    change source50.get? (0 + index) = destination50_0.get? index
    have same : source50 = destination50_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length50 : (target50.map Setup.Block.length).sum = source50.length := by decide +kernel

noncomputable def source51 : Setup.Block := original.get ⟨51, by decide +kernel⟩

column_blocks_part part51_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 34 stop 35
noncomputable def destination51_0 : Setup.Block := part51_0.get ⟨0, by decide +kernel⟩

noncomputable def target51 : List Setup.Block := part51_0

theorem follows51 : blockTargetsFollow source51 0 target51 :=
  And.intro (by
    intro index bounded
    change source51.get? (0 + index) = destination51_0.get? index
    have same : source51 = destination51_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length51 : (target51.map Setup.Block.length).sum = source51.length := by decide +kernel

noncomputable def source52 : Setup.Block := original.get ⟨52, by decide +kernel⟩

column_blocks_part part52_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 35 stop 36
noncomputable def destination52_0 : Setup.Block := part52_0.get ⟨0, by decide +kernel⟩

noncomputable def target52 : List Setup.Block := part52_0

theorem follows52 : blockTargetsFollow source52 0 target52 :=
  And.intro (by
    intro index bounded
    change source52.get? (0 + index) = destination52_0.get? index
    have same : source52 = destination52_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length52 : (target52.map Setup.Block.length).sum = source52.length := by decide +kernel

noncomputable def source53 : Setup.Block := original.get ⟨53, by decide +kernel⟩

column_blocks_part part53_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 36 stop 37
noncomputable def destination53_0 : Setup.Block := part53_0.get ⟨0, by decide +kernel⟩

noncomputable def target53 : List Setup.Block := part53_0

theorem follows53 : blockTargetsFollow source53 0 target53 :=
  And.intro (by
    intro index bounded
    change source53.get? (0 + index) = destination53_0.get? index
    have same : source53 = destination53_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length53 : (target53.map Setup.Block.length).sum = source53.length := by decide +kernel

noncomputable def source54 : Setup.Block := original.get ⟨54, by decide +kernel⟩

column_blocks_part part54_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 37 stop 38
noncomputable def destination54_0 : Setup.Block := part54_0.get ⟨0, by decide +kernel⟩

noncomputable def target54 : List Setup.Block := part54_0

theorem follows54 : blockTargetsFollow source54 0 target54 :=
  And.intro (by
    intro index bounded
    change source54.get? (0 + index) = destination54_0.get? index
    have same : source54 = destination54_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length54 : (target54.map Setup.Block.length).sum = source54.length := by decide +kernel

noncomputable def source55 : Setup.Block := original.get ⟨55, by decide +kernel⟩

column_blocks_part part55_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 38 stop 39
noncomputable def destination55_0 : Setup.Block := part55_0.get ⟨0, by decide +kernel⟩

noncomputable def target55 : List Setup.Block := part55_0

theorem follows55 : blockTargetsFollow source55 0 target55 :=
  And.intro (by
    intro index bounded
    change source55.get? (0 + index) = destination55_0.get? index
    have same : source55 = destination55_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length55 : (target55.map Setup.Block.length).sum = source55.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0
