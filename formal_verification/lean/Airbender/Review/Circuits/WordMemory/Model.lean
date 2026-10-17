import Airbender.Review.Circuits.WordMemory.Artifact
import Airbender.Review.Helpers.Properties

namespace Airbender.WordMemory

/-- Canonical native source, decoded immediate and ranged effective address. -/
def sourceWord {p : Nat} (w : Nat → ZMod p) : Arithmetic.Word := ⟨(w 17).val, (w 18).val⟩
def immediateWord {p : Nat} (w : Nat → ZMod p) : Arithmetic.Word := ⟨(w 9).val, (w 10).val⟩
def addressWord {p : Nat} (w : Nat → ZMod p) : Arithmetic.Word := ⟨(w 19).val, (w 20).val⟩

/-- Native transfer observables. The README names every column. Bounded address
    arithmetic and public decoder recovery are checked separately. Initialized
    logical ranges/history are checked; actual Sail port reads and instruction
    execution remain open. -/
structure NativeTransfers {p : Nat} (rom : Verification.WordROM) (w : Nat → ZMod p) : Prop where
  storeBit : w 12 = 0 ∨ w 12 = 1
  addressBounds : (w 19).val < 65536 ∧ (w 20).val < 65536
  addressAlignment : (w 19).val % 4 = 0
  readAddress : w 28 = (1 - w 12) * w 19 + w 12 * w 6 ∧
    w 29 = (1 - w 12) * w 20
  writeAddress : w 32 = 1 - w 12 ∧
    w 33 = w 12 * w 19 + (1 - w 12) * w 7 ∧ w 34 = w 12 * w 20
  load : w 12 = 0 →
    let value := rom.word (((w 19).val + 65536 * ((w 20).val % 64)) / 4)
    w 37 = (1 - w 8) * (if (w 20).val < 64 then ((value.toNat % 65536 : Nat) : ZMod p) else w 30) ∧
    w 38 = (1 - w 8) * (if (w 20).val < 64 then ((value.toNat / 65536 : Nat) : ZMod p) else w 31)
  store : w 12 = 1 → 64 ≤ (w 20).val ∧ w 37 = w 30 ∧ w 38 = w 31

end Airbender.WordMemory
