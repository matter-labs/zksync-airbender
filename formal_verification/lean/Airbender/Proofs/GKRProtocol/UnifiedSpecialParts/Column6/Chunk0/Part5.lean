import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column6.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source40 : Setup.Block := original.get ⟨40, by decide +kernel⟩

column_blocks_part part40_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 40 stop 41
noncomputable def destination40_0 : Setup.Block := part40_0.get ⟨0, by decide +kernel⟩

noncomputable def target40 : List Setup.Block := part40_0

theorem follows40 : blockTargetsFollow source40 0 target40 :=
  And.intro (by
    intro index bounded
    change source40.get? (0 + index) = destination40_0.get? index
    have same : source40 = destination40_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length40 : (target40.map Setup.Block.length).sum = source40.length := by decide +kernel

noncomputable def source41 : Setup.Block := original.get ⟨41, by decide +kernel⟩

column_blocks_part part41_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 41 stop 42
noncomputable def destination41_0 : Setup.Block := part41_0.get ⟨0, by decide +kernel⟩

noncomputable def target41 : List Setup.Block := part41_0

theorem follows41 : blockTargetsFollow source41 0 target41 :=
  And.intro (by
    intro index bounded
    change source41.get? (0 + index) = destination41_0.get? index
    have same : source41 = destination41_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length41 : (target41.map Setup.Block.length).sum = source41.length := by decide +kernel

noncomputable def source42 : Setup.Block := original.get ⟨42, by decide +kernel⟩

column_blocks_part part42_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 42 stop 43
noncomputable def destination42_0 : Setup.Block := part42_0.get ⟨0, by decide +kernel⟩

noncomputable def target42 : List Setup.Block := part42_0

theorem follows42 : blockTargetsFollow source42 0 target42 :=
  And.intro (by
    intro index bounded
    change source42.get? (0 + index) = destination42_0.get? index
    have same : source42 = destination42_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length42 : (target42.map Setup.Block.length).sum = source42.length := by decide +kernel

noncomputable def source43 : Setup.Block := original.get ⟨43, by decide +kernel⟩

column_blocks_part part43_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 43 stop 44
noncomputable def destination43_0 : Setup.Block := part43_0.get ⟨0, by decide +kernel⟩

noncomputable def target43 : List Setup.Block := part43_0

theorem follows43 : blockTargetsFollow source43 0 target43 :=
  And.intro (by
    intro index bounded
    change source43.get? (0 + index) = destination43_0.get? index
    have same : source43 = destination43_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length43 : (target43.map Setup.Block.length).sum = source43.length := by decide +kernel

noncomputable def source44 : Setup.Block := original.get ⟨44, by decide +kernel⟩

column_blocks_part part44_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 44 stop 45
noncomputable def destination44_0 : Setup.Block := part44_0.get ⟨0, by decide +kernel⟩

noncomputable def target44 : List Setup.Block := part44_0

theorem follows44 : blockTargetsFollow source44 0 target44 :=
  And.intro (by
    intro index bounded
    change source44.get? (0 + index) = destination44_0.get? index
    have same : source44 = destination44_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length44 : (target44.map Setup.Block.length).sum = source44.length := by decide +kernel

noncomputable def source45 : Setup.Block := original.get ⟨45, by decide +kernel⟩

column_blocks_part part45_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 45 stop 46
noncomputable def destination45_0 : Setup.Block := part45_0.get ⟨0, by decide +kernel⟩

noncomputable def target45 : List Setup.Block := part45_0

theorem follows45 : blockTargetsFollow source45 0 target45 :=
  And.intro (by
    intro index bounded
    change source45.get? (0 + index) = destination45_0.get? index
    have same : source45 = destination45_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length45 : (target45.map Setup.Block.length).sum = source45.length := by decide +kernel

noncomputable def source46 : Setup.Block := original.get ⟨46, by decide +kernel⟩

column_blocks_part part46_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 46 stop 47
noncomputable def destination46_0 : Setup.Block := part46_0.get ⟨0, by decide +kernel⟩

noncomputable def target46 : List Setup.Block := part46_0

theorem follows46 : blockTargetsFollow source46 0 target46 :=
  And.intro (by
    intro index bounded
    change source46.get? (0 + index) = destination46_0.get? index
    have same : source46 = destination46_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length46 : (target46.map Setup.Block.length).sum = source46.length := by decide +kernel

noncomputable def source47 : Setup.Block := original.get ⟨47, by decide +kernel⟩

column_blocks_part part47_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 47 stop 48
noncomputable def destination47_0 : Setup.Block := part47_0.get ⟨0, by decide +kernel⟩

noncomputable def target47 : List Setup.Block := part47_0

theorem follows47 : blockTargetsFollow source47 0 target47 :=
  And.intro (by
    intro index bounded
    change source47.get? (0 + index) = destination47_0.get? index
    have same : source47 = destination47_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length47 : (target47.map Setup.Block.length).sum = source47.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk0
