import Airbender.Reference.Compiler.ProgramSetup

namespace Airbender.Reference.Compiler.ProgramSetup
set_option warningAsError true
set_option Elab.async false
variable {F : Type} [Ring F] [DecidableEq F]

theorem fixed_group (layout : Layout) (fixed : Fin 3 → Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32)
    (group : Fin 3) (index : Nat) (other : group.val ≠ 0) :
    groupRows layout fixed decoder wordAt group index = fixed group index := by
  simp [groupRows, other]

theorem tagged_fixed (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true)
    (notDecoder : (fixed index).getLast?.getD 0 ≠ 46)
    (notROM : (fixed index).getLast?.getD 0 ≠ 34) :
    genericRows layout fixed decoder wordAt index = fixed index := by
  simp [genericRows, tagged, notDecoder, notROM]

theorem untagged_decoder (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (untagged : layout.tagged = false)
    (inside : inRegion layout.decoderStart layout.decoderWords index) :
    genericRows layout fixed decoder wordAt index =
      decoder[index - layout.decoderStart]?.getD (decoderPadding layout.width) := by
  simp [genericRows, untagged, inside]

theorem untagged_padding (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (untagged : layout.tagged = false)
    (outside : ¬inRegion layout.decoderStart layout.decoderWords index) :
    genericRows layout fixed decoder wordAt index = decoderPadding layout.width := by
  simp [genericRows, untagged, outside]

theorem tagged_decoder (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true) (tag : (fixed index).getLast?.getD 0 = 46)
    (inside : inRegion layout.decoderStart layout.decoderWords index) :
    genericRows layout fixed decoder wordAt index =
      packTagged layout.width 46
        (decoder[index - layout.decoderStart]?.getD (decoderPadding (layout.width - 1))) := by
  simp [genericRows, tagged, tag, inside]

theorem tagged_rom (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index start : Nat)
    (tagged : layout.tagged = true) (tag : (fixed index).getLast?.getD 0 = 34)
    (different : (34 : F) ≠ 46) (rom : layout.romStart = some start)
    (inside : inRegion start layout.romWords index) :
    genericRows layout fixed decoder wordAt index =
      packTagged layout.width 34 (romPayload wordAt (index - start)) := by
  simp [genericRows, tagged, tag, different, rom, inside]

omit [DecidableEq F] in
theorem packTagged_payload (width : Nat) (tag : F) (payload : List F) :
    (packTagged width tag payload).take payload.length = payload := by
  simp [packTagged]

omit [DecidableEq F] in
theorem packTagged_tag (width : Nat) (tag : F) (payload : List F) :
    (packTagged width tag payload).getLast? = some tag := by
  simp [packTagged]

omit [DecidableEq F] in
theorem packTagged_injective (width : Nat) (tag : F) (left right : List F)
    (lengths : left.length = right.length)
    (same : packTagged width tag left = packTagged width tag right) : left = right := by
  calc
    left = (packTagged width tag left).take left.length := (packTagged_payload _ _ _).symm
    _ = (packTagged width tag right).take left.length := congrArg (List.take left.length) same
    _ = right := by rw [lengths]; exact packTagged_payload _ _ _

omit [DecidableEq F] in
theorem decoderPadding_head (width : Nat) (positive : 0 < width) :
    (decoderPadding (F := F) width).head? = some (-1) := by
  cases width with
  | zero => omega
  | succ width => simp [decoderPadding, List.replicate_succ]

end Airbender.Reference.Compiler.ProgramSetup
