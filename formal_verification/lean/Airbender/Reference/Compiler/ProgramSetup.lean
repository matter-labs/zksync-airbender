import Mathlib.Algebra.Ring.Defs

namespace Airbender.Reference.Compiler.ProgramSetup

/-- Public geometry of the program regions in a native generic lookup table. -/
structure Layout where
  width : Nat
  tagged : Bool
  decoderStart : Nat
  decoderWords : Nat
  romStart : Option Nat
  romWords : Nat

variable {F : Type} [Ring F] [DecidableEq F]

abbrev inRegion (start count index : Nat) : Prop :=
  start ≤ index ∧ index - start < count

def decoderPadding (width : Nat) : List F := List.replicate width (-1)

/-- Pad after the payload and retain every supplied field. -/
def packTagged (width : Nat) (tag : F) (payload : List F) : List F :=
  payload ++ List.replicate (width - (payload.length + 1)) 0 ++ [tag]

def romPayload (wordAt : Nat → BitVec 32) (index : Nat) : List F :=
  [((4 * index : Nat) : F), ((wordAt index).toNat % 65536 : Nat),
    ((wordAt index).toNat / 65536 : Nat)]

/-- Replace program rows through the native decoder and ROM discriminators.
The caller supplies decoder rows and the public ROM word function. -/
def genericRows (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat) : List F :=
  if layout.tagged then
    let previous := fixed index
    let tag := previous.getLast?.getD 0
    if tag = 46 then
      if inRegion layout.decoderStart layout.decoderWords index then
        packTagged layout.width 46
          (decoder[index - layout.decoderStart]?.getD (decoderPadding (layout.width - 1)))
      else List.replicate layout.width 0
    else if tag = 34 then
      match layout.romStart with
      | none => List.replicate layout.width 0
      | some start =>
        if inRegion start layout.romWords index then
          packTagged layout.width 34 (romPayload wordAt (index - start))
        else List.replicate layout.width 0
    else previous
  else if inRegion layout.decoderStart layout.decoderWords index then
    decoder[index - layout.decoderStart]?.getD (decoderPadding layout.width)
  else decoderPadding layout.width

/-- Range and timestamp groups keep their native setup rows. -/
def groupRows (layout : Layout) (fixed : Fin 3 → Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32)
    (group : Fin 3) (index : Nat) : List F :=
  if group.val = 0 then genericRows layout (fixed group) decoder wordAt index
  else fixed group index

end Airbender.Reference.Compiler.ProgramSetup
