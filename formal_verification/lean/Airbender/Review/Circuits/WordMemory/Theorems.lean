import Airbender.Review.Circuits.WordMemory.Model
import Airbender.Proofs.WordMemory.Transfers
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory

/-- Native v2 port selection, aligned address limbs, masked RAM/ROM loads and
    RAM-only stores. Public decoding, initialized reads and Sail execution are
    subsequent milestones; this statement is solely about native transfers. -/
theorem native_transfers (rom : Verification.WordROM) (w : Nat → ZMod mersenne31Modulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom) →
    NativeTransfers rom w :=
  Proofs.transfers (by decide)

end Airbender.WordMemory
