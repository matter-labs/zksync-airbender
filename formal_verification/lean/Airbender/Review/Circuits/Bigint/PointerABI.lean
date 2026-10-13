import Airbender.Review.Circuits.Bigint.Addresses
import Airbender.Review.Helpers.Delegation.Memory
import Airbender.Review.Helpers.ROM

namespace Airbender.Bigint.Addresses

/-- x10/x11's pointer words, observed at their imported register ports.
    This identifies the inputs; shared initialized history supplies their ranges. -/
def nativeInput (w : Nat → ZMod p) : Input :=
  ⟨(Trace.readToken w importedConstraintsMemoryPorts[0]).word,
    (Trace.readToken w importedConstraintsMemoryPorts[9]).word⟩

/-- The pointer part of the project's bigint call ABI. Control-mask validity
    and operation effects are separate. No pointer condition is supplied per row. -/
structure PointerABI (input : Input) : Prop where
  /-- The imported pointer words have canonical sixteen-bit limbs. -/
  bounded : input.left.Bounded ∧ input.right.Bounded
  /-- Both blocks start above the public ROM boundary. -/
  ram : Trace.ROM.limit ≤ input.left.toBitVec.toNat ∧
    Trace.ROM.limit ≤ input.right.toBitVec.toNat
  /-- Both 256-bit blocks start at thirty-two-byte-aligned addresses. -/
  aligned : input.left.toBitVec.toNat % 32 = 0 ∧ input.right.toBitVec.toNat % 32 = 0
  /-- The two blocks have different bases, as required by the project reference. -/
  distinct : input.left.toBitVec ≠ input.right.toBitVec

end Airbender.Bigint.Addresses
