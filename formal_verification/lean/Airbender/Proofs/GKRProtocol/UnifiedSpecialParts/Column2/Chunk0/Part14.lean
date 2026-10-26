import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source112 : Setup.Block := original.get ⟨112, by decide +kernel⟩

column_blocks_part part112_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 95 stop 96
noncomputable def destination112_0 : Setup.Block := part112_0.get ⟨0, by decide +kernel⟩

noncomputable def target112 : List Setup.Block := part112_0

theorem follows112 : blockTargetsFollow source112 0 target112 :=
  And.intro (by
    intro index bounded
    change source112.get? (0 + index) = destination112_0.get? index
    have same : source112 = destination112_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length112 : (target112.map Setup.Block.length).sum = source112.length := by decide +kernel

noncomputable def source113 : Setup.Block := original.get ⟨113, by decide +kernel⟩

column_blocks_part part113_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 96 stop 97
noncomputable def destination113_0 : Setup.Block := part113_0.get ⟨0, by decide +kernel⟩

noncomputable def target113 : List Setup.Block := part113_0

theorem follows113 : blockTargetsFollow source113 0 target113 :=
  And.intro (by
    intro index bounded
    change source113.get? (0 + index) = destination113_0.get? index
    have same : source113 = destination113_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length113 : (target113.map Setup.Block.length).sum = source113.length := by decide +kernel

noncomputable def source114 : Setup.Block := original.get ⟨114, by decide +kernel⟩

column_blocks_part part114_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 97 stop 98
noncomputable def destination114_0 : Setup.Block := part114_0.get ⟨0, by decide +kernel⟩

noncomputable def target114 : List Setup.Block := part114_0

theorem follows114 : blockTargetsFollow source114 0 target114 :=
  And.intro (by
    intro index bounded
    change source114.get? (0 + index) = destination114_0.get? index
    have same : source114 = destination114_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length114 : (target114.map Setup.Block.length).sum = source114.length := by decide +kernel

noncomputable def source115 : Setup.Block := original.get ⟨115, by decide +kernel⟩

column_blocks_part part115_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 98 stop 99
noncomputable def destination115_0 : Setup.Block := part115_0.get ⟨0, by decide +kernel⟩

noncomputable def target115 : List Setup.Block := part115_0

theorem follows115 : blockTargetsFollow source115 0 target115 :=
  And.intro (by
    intro index bounded
    change source115.get? (0 + index) = destination115_0.get? index
    have same : source115 = destination115_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length115 : (target115.map Setup.Block.length).sum = source115.length := by decide +kernel

noncomputable def source116 : Setup.Block := original.get ⟨116, by decide +kernel⟩

column_blocks_part part116_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 99 stop 100
noncomputable def destination116_0 : Setup.Block := part116_0.get ⟨0, by decide +kernel⟩

noncomputable def target116 : List Setup.Block := part116_0

theorem follows116 : blockTargetsFollow source116 0 target116 :=
  And.intro (by
    intro index bounded
    change source116.get? (0 + index) = destination116_0.get? index
    have same : source116 = destination116_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length116 : (target116.map Setup.Block.length).sum = source116.length := by decide +kernel

noncomputable def source117 : Setup.Block := original.get ⟨117, by decide +kernel⟩

column_blocks_part part117_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 100 stop 101
noncomputable def destination117_0 : Setup.Block := part117_0.get ⟨0, by decide +kernel⟩

noncomputable def target117 : List Setup.Block := part117_0

theorem follows117 : blockTargetsFollow source117 0 target117 :=
  And.intro (by
    intro index bounded
    change source117.get? (0 + index) = destination117_0.get? index
    have same : source117 = destination117_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length117 : (target117.map Setup.Block.length).sum = source117.length := by decide +kernel

noncomputable def source118 : Setup.Block := original.get ⟨118, by decide +kernel⟩

column_blocks_part part118_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 101 stop 102
noncomputable def destination118_0 : Setup.Block := part118_0.get ⟨0, by decide +kernel⟩

noncomputable def target118 : List Setup.Block := part118_0

theorem follows118 : blockTargetsFollow source118 0 target118 :=
  And.intro (by
    intro index bounded
    change source118.get? (0 + index) = destination118_0.get? index
    have same : source118 = destination118_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length118 : (target118.map Setup.Block.length).sum = source118.length := by decide +kernel

noncomputable def source119 : Setup.Block := original.get ⟨119, by decide +kernel⟩

column_blocks_part part119_0 from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 102 stop 103
noncomputable def destination119_0 : Setup.Block := part119_0.get ⟨0, by decide +kernel⟩

noncomputable def target119 : List Setup.Block := part119_0

theorem follows119 : blockTargetsFollow source119 0 target119 :=
  And.intro (by
    intro index bounded
    change source119.get? (0 + index) = destination119_0.get? index
    have same : source119 = destination119_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length119 : (target119.map Setup.Block.length).sum = source119.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0
