import Airbender.Review.Circuits.Blake2Worker.DiagonalG

namespace Airbender.NativeWorkerExtendedOutput
open Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
/-- Actual extended-state memory write, in A/B/C/D order. -/
def writeLimb (w : Nat → F) (word : Fin 16) (limb : Fin 2) : F := w (38+4*word.val+limb.val)
def writeWord (w : Nat → F) (word : Fin 16) : BitVec 32 := pack (writeLimb w word 0) (writeLimb w word 1)
/-- Native diagonal d updates component c at its original column d+c. -/
def destination (diagonal component : Fin 4) : Fin 16 :=
  ⟨4*component.val+(diagonal.val+component.val)%4,by have := component.isLt; have := Nat.mod_lt (diagonal.val+component.val) (by decide : 0<4); omega⟩
def componentOf (word : Fin 16) : Fin 4 := ⟨word.val/4,by have := word.isLt; omega⟩
def diagonalOf (word : Fin 16) : Fin 4 := ⟨(word.val%4+4-word.val/4)%4,Nat.mod_lt _ (by decide)⟩
def bLimb (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  if limb.val = 0 then w (493+44*diagonal.val)+512*w (494+44*diagonal.val)
  else w (495+44*diagonal.val)+512*w (492+44*diagonal.val)
def resultLimb (w : Nat → F) (diagonal component : Fin 4) (limb : Fin 2) : F :=
  match component.val with
  | 0 => Airbender.NativeWorkerDiagonalAD.sumLimb w diagonal limb
  | 1 => bLimb w diagonal limb
  | 2 => Airbender.NativeWorkerDiagonalG.cLimb w diagonal limb
  | _ => Airbender.NativeWorkerDiagonalG.dLimb w diagonal limb
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerDiagonalG.RowEffects w
  limbs : ∀ diagonal component : Fin 4, ∀ limb : Fin 2,
    writeLimb w (destination diagonal component) limb = resultLimb w diagonal component limb
  written : ∀ word : Fin 16, writeWord w word =
    (Airbender.NativeWorkerDiagonalG.diagonalResult w (diagonalOf word))[componentOf word]
  result : ∀ word : Fin 16, writeWord w word = (Airbender.NativeWorkerSecondCB.g
    (Airbender.NativeWorkerDiagonalFirst.inputWord w (diagonalOf word) 0)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w (diagonalOf word) 1)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w (diagonalOf word) 2)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w (diagonalOf word) 3)
    (Airbender.NativeWorkerAddition.messageWord w ⟨8+2*(diagonalOf word).val,by have := (diagonalOf word).isLt; omega⟩)
    (Airbender.NativeWorkerAddition.messageWord w ⟨9+2*(diagonalOf word).val,by have := (diagonalOf word).isLt; omega⟩))[componentOf word]
end Airbender.NativeWorkerExtendedOutput
