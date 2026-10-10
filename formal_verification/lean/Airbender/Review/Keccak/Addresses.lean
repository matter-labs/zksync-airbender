import Airbender.Review.Keccak.Theta

namespace Airbender.Keccak
open Arithmetic

/-- Canonical pointer observed at the imported x11 read. Initialized history
    supplies its limb bounds; the circuit supplies its 256-byte alignment. -/
def statePointer {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 13).val, (w 14).val⟩

/-- Address interpretation of the twelve actual JSON ports, not a claim about
    global memory enforcement. Each selected 64-bit lane supplies two words. -/
structure AddressChecks {p : Nat} (w : Nat → ZMod p) : Prop where
  aligned : (statePointer w).lo % 256 = 0
  laneIndices : ∀ i : Fin 6, (w (7 + i.val)).val < 31
  noCarry : ∀ i : Fin 12, (statePointer w).lo +
    8 * (w (7 + i.val / 2)).val + 4 * (i.val % 2) < limbBase
  addresses : ∀ i : Fin 12, importedConstraintsIndirectPorts[i].address w =
    (statePointer w).toBitVec + BitVec.ofNat 32
      (8 * (w (7 + i.val / 2)).val + 4 * (i.val % 2))

end Airbender.Keccak
