import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk206.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk206
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source26368 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part26368_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 910 stop 911
noncomputable def destination26368_0 : Setup.Block := part26368_0.get ⟨0, by decide +kernel⟩

noncomputable def target26368 : List Setup.Block := part26368_0

theorem follows26368 : blockTargetsFollow source26368 0 target26368 :=
  And.intro (by
    intro index bounded
    change source26368.get? (0 + index) = destination26368_0.get? index
    have same : source26368 = destination26368_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26368 : (target26368.map Setup.Block.length).sum = source26368.length := by decide +kernel

noncomputable def source26369 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part26369_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 911 stop 912
noncomputable def destination26369_0 : Setup.Block := part26369_0.get ⟨0, by decide +kernel⟩

noncomputable def target26369 : List Setup.Block := part26369_0

theorem follows26369 : blockTargetsFollow source26369 0 target26369 :=
  And.intro (by
    intro index bounded
    change source26369.get? (0 + index) = destination26369_0.get? index
    have same : source26369 = destination26369_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26369 : (target26369.map Setup.Block.length).sum = source26369.length := by decide +kernel

noncomputable def source26370 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part26370_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 912 stop 913
noncomputable def destination26370_0 : Setup.Block := part26370_0.get ⟨0, by decide +kernel⟩

noncomputable def target26370 : List Setup.Block := part26370_0

theorem follows26370 : blockTargetsFollow source26370 0 target26370 :=
  And.intro (by
    intro index bounded
    change source26370.get? (0 + index) = destination26370_0.get? index
    have same : source26370 = destination26370_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26370 : (target26370.map Setup.Block.length).sum = source26370.length := by decide +kernel

noncomputable def source26371 : Setup.Block := original.get ⟨3, by decide +kernel⟩

column_blocks_part part26371_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 913 stop 914
noncomputable def destination26371_0 : Setup.Block := part26371_0.get ⟨0, by decide +kernel⟩

noncomputable def target26371 : List Setup.Block := part26371_0

theorem follows26371 : blockTargetsFollow source26371 0 target26371 :=
  And.intro (by
    intro index bounded
    change source26371.get? (0 + index) = destination26371_0.get? index
    have same : source26371 = destination26371_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26371 : (target26371.map Setup.Block.length).sum = source26371.length := by decide +kernel

noncomputable def source26372 : Setup.Block := original.get ⟨4, by decide +kernel⟩

column_blocks_part part26372_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 914 stop 915
noncomputable def destination26372_0 : Setup.Block := part26372_0.get ⟨0, by decide +kernel⟩

noncomputable def target26372 : List Setup.Block := part26372_0

theorem follows26372 : blockTargetsFollow source26372 0 target26372 :=
  And.intro (by
    intro index bounded
    change source26372.get? (0 + index) = destination26372_0.get? index
    have same : source26372 = destination26372_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26372 : (target26372.map Setup.Block.length).sum = source26372.length := by decide +kernel

noncomputable def source26373 : Setup.Block := original.get ⟨5, by decide +kernel⟩

column_blocks_part part26373_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 915 stop 916
noncomputable def destination26373_0 : Setup.Block := part26373_0.get ⟨0, by decide +kernel⟩

noncomputable def target26373 : List Setup.Block := part26373_0

theorem follows26373 : blockTargetsFollow source26373 0 target26373 :=
  And.intro (by
    intro index bounded
    change source26373.get? (0 + index) = destination26373_0.get? index
    have same : source26373 = destination26373_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26373 : (target26373.map Setup.Block.length).sum = source26373.length := by decide +kernel

noncomputable def source26374 : Setup.Block := original.get ⟨6, by decide +kernel⟩

column_blocks_part part26374_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 916 stop 917
noncomputable def destination26374_0 : Setup.Block := part26374_0.get ⟨0, by decide +kernel⟩

noncomputable def target26374 : List Setup.Block := part26374_0

theorem follows26374 : blockTargetsFollow source26374 0 target26374 :=
  And.intro (by
    intro index bounded
    change source26374.get? (0 + index) = destination26374_0.get? index
    have same : source26374 = destination26374_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26374 : (target26374.map Setup.Block.length).sum = source26374.length := by decide +kernel

noncomputable def source26375 : Setup.Block := original.get ⟨7, by decide +kernel⟩

column_blocks_part part26375_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 917 stop 918
noncomputable def destination26375_0 : Setup.Block := part26375_0.get ⟨0, by decide +kernel⟩

noncomputable def target26375 : List Setup.Block := part26375_0

theorem follows26375 : blockTargetsFollow source26375 0 target26375 :=
  And.intro (by
    intro index bounded
    change source26375.get? (0 + index) = destination26375_0.get? index
    have same : source26375 = destination26375_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26375 : (target26375.map Setup.Block.length).sum = source26375.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk206
