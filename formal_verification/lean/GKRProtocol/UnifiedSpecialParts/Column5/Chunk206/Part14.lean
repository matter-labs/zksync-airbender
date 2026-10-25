import GKRProtocol.UnifiedSpecialParts.Column5.Chunk206.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk206
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source26480 : Setup.Block := original.get ⟨112, by decide +kernel⟩

column_blocks_part part26480_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1022 stop 1023
noncomputable def destination26480_0 : Setup.Block := part26480_0.get ⟨0, by decide +kernel⟩

noncomputable def target26480 : List Setup.Block := part26480_0

theorem follows26480 : blockTargetsFollow source26480 0 target26480 :=
  And.intro (by
    intro index bounded
    change source26480.get? (0 + index) = destination26480_0.get? index
    have same : source26480 = destination26480_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26480 : (target26480.map Setup.Block.length).sum = source26480.length := by decide +kernel

noncomputable def source26481 : Setup.Block := original.get ⟨113, by decide +kernel⟩

column_blocks_part part26481_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1023 stop 1024
noncomputable def destination26481_0 : Setup.Block := part26481_0.get ⟨0, by decide +kernel⟩

noncomputable def target26481 : List Setup.Block := part26481_0

theorem follows26481 : blockTargetsFollow source26481 0 target26481 :=
  And.intro (by
    intro index bounded
    change source26481.get? (0 + index) = destination26481_0.get? index
    have same : source26481 = destination26481_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26481 : (target26481.map Setup.Block.length).sum = source26481.length := by decide +kernel

noncomputable def source26482 : Setup.Block := original.get ⟨114, by decide +kernel⟩

column_blocks_part part26482_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1024 stop 1025
noncomputable def destination26482_0 : Setup.Block := part26482_0.get ⟨0, by decide +kernel⟩

noncomputable def target26482 : List Setup.Block := part26482_0

theorem follows26482 : blockTargetsFollow source26482 0 target26482 :=
  And.intro (by
    intro index bounded
    change source26482.get? (0 + index) = destination26482_0.get? index
    have same : source26482 = destination26482_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26482 : (target26482.map Setup.Block.length).sum = source26482.length := by decide +kernel

noncomputable def source26483 : Setup.Block := original.get ⟨115, by decide +kernel⟩

column_blocks_part part26483_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1025 stop 1026
noncomputable def destination26483_0 : Setup.Block := part26483_0.get ⟨0, by decide +kernel⟩

noncomputable def target26483 : List Setup.Block := part26483_0

theorem follows26483 : blockTargetsFollow source26483 0 target26483 :=
  And.intro (by
    intro index bounded
    change source26483.get? (0 + index) = destination26483_0.get? index
    have same : source26483 = destination26483_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26483 : (target26483.map Setup.Block.length).sum = source26483.length := by decide +kernel

noncomputable def source26484 : Setup.Block := original.get ⟨116, by decide +kernel⟩

column_blocks_part part26484_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1026 stop 1027
noncomputable def destination26484_0 : Setup.Block := part26484_0.get ⟨0, by decide +kernel⟩

noncomputable def target26484 : List Setup.Block := part26484_0

theorem follows26484 : blockTargetsFollow source26484 0 target26484 :=
  And.intro (by
    intro index bounded
    change source26484.get? (0 + index) = destination26484_0.get? index
    have same : source26484 = destination26484_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26484 : (target26484.map Setup.Block.length).sum = source26484.length := by decide +kernel

noncomputable def source26485 : Setup.Block := original.get ⟨117, by decide +kernel⟩

column_blocks_part part26485_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1027 stop 1028
noncomputable def destination26485_0 : Setup.Block := part26485_0.get ⟨0, by decide +kernel⟩

noncomputable def target26485 : List Setup.Block := part26485_0

theorem follows26485 : blockTargetsFollow source26485 0 target26485 :=
  And.intro (by
    intro index bounded
    change source26485.get? (0 + index) = destination26485_0.get? index
    have same : source26485 = destination26485_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26485 : (target26485.map Setup.Block.length).sum = source26485.length := by decide +kernel

noncomputable def source26486 : Setup.Block := original.get ⟨118, by decide +kernel⟩

column_blocks_part part26486_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1028 stop 1029
noncomputable def destination26486_0 : Setup.Block := part26486_0.get ⟨0, by decide +kernel⟩

noncomputable def target26486 : List Setup.Block := part26486_0

theorem follows26486 : blockTargetsFollow source26486 0 target26486 :=
  And.intro (by
    intro index bounded
    change source26486.get? (0 + index) = destination26486_0.get? index
    have same : source26486 = destination26486_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26486 : (target26486.map Setup.Block.length).sum = source26486.length := by decide +kernel

noncomputable def source26487 : Setup.Block := original.get ⟨119, by decide +kernel⟩

column_blocks_part part26487_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1029 stop 1030
noncomputable def destination26487_0 : Setup.Block := part26487_0.get ⟨0, by decide +kernel⟩

noncomputable def target26487 : List Setup.Block := part26487_0

theorem follows26487 : blockTargetsFollow source26487 0 target26487 :=
  And.intro (by
    intro index bounded
    change source26487.get? (0 + index) = destination26487_0.get? index
    have same : source26487 = destination26487_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26487 : (target26487.map Setup.Block.length).sum = source26487.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk206
