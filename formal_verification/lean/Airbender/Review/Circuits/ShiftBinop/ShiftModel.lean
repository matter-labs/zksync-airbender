import Airbender.Review.Circuits.ShiftBinop.BinaryModel

namespace Airbender.ShiftBinop
open Arithmetic Verification
set_option autoImplicit false

inductive ShiftKind where
  | sll | srl | sra
  deriving DecidableEq

def ShiftKind.operation : ShiftKind → Operation
  | .sll => .sll | .srl => .srl | .sra => .sra

inductive ShiftPart where
  | sllLow | sllHigh | srlLow | srlHigh | signFill | zero
  deriving DecidableEq

def ShiftPart.tag : ShiftPart → Nat
  | .sllLow => 48 | .sllHigh => 49 | .srlLow => 50
  | .srlHigh => 51 | .signFill => 52 | .zero => 0

/-- Literal RV32 contribution of a canonical native packed key. Its connection
    to a bounded source read is a subsequent initialized-history obligation. -/
def ShiftPart.result (part : ShiftPart) (key : Nat) : BitVec 32 :=
  match part with
  | .sllLow => (BitVec.ofNat 32 (key % 65536)) <<< (key / 65536)
  | .sllHigh => (BitVec.ofNat 32 ((key % 65536) * 65536)) <<< (key / 65536)
  | .srlLow => (BitVec.ofNat 32 (key % 65536)) >>> (key / 65536)
  | .srlHigh => (BitVec.ofNat 32 ((key % 65536) * 65536)) >>> (key / 65536)
  | .signFill => if key % 65536 < 32768 then 0
      else (BitVec.allOnes 32) <<< (32 - key / 65536)
  | .zero => 0

def ShiftKind.parts : ShiftKind → Vector ShiftPart 3
  | .sll => #v[.sllLow,.sllHigh,.zero]
  | .srl => #v[.srlLow,.srlHigh,.zero]
  | .sra => #v[.signFill,.srlLow,.srlHigh]

/-- Logical input column of each packed native contribution; zero has no input. -/
def ShiftKind.sourceColumn (kind : ShiftKind) (slot : Fin 3) : Nat :=
  match kind with
  | .sll | .srl => if slot.val = 0 then 23 else 24
  | .sra => if slot.val = 1 then 23 else 24

def partQuery (w : Nat → ZMod mersenne31Modulus) (slot : Fin 3) :=
  #v[w (43 + 4 * slot.val),w (44 + 4 * slot.val),w (45 + 4 * slot.val)]
def partWord (w : Nat → ZMod mersenne31Modulus) (slot : Fin 3) : Word :=
  ⟨(w (44 + 4 * slot.val)).val,(w (45 + 4 * slot.val)).val⟩

/-- Native contribution semantics and assembly, without assuming source ranges,
    table equivalence, individual operation flags or an expected selected word. -/
structure ShiftContributions (w : Nat → ZMod mersenne31Modulus) (kind : ShiftKind) : Prop where
  operandLowBound : (w 27).val < 65536
  amount : (w 29).val = (w 27).val % 32
  truncationPadding : w 30 = 0
  keys : ∀ slot : Fin 3, w (43 + 4 * slot.val) =
    if kind.parts[slot.val] = .zero then 0 else w (kind.sourceColumn slot) + 65536 * w 29
  parts : ∀ slot : Fin 3, (w (43 + 4 * slot.val)).val < 2097152 ∧
    (partWord w slot).Bounded ∧ (partWord w slot).toBitVec =
      (kind.parts[slot.val]).result (w (43 + 4 * slot.val)).val
  selectedLow : (w 55).val = (w 44).val + (w 48).val + (w 52).val
  selectedHigh : (w 56).val = (w 45).val + (w 49).val + (w 53).val
  selected : (selectedWord w).toBitVec =
    (partWord w 0).toBitVec + (partWord w 1).toBitVec + (partWord w 2).toBitVec

end Airbender.ShiftBinop
