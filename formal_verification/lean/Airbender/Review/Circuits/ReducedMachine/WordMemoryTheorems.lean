import Airbender.Proofs.ReducedMachine.NativeWordMemoryFields

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false

/-- Accepted actual native equations derive word-only operand/port-space routing.
    Decoded mask stays explicit; original memory, ROM and execution stay separate. -/
theorem word_memory_routing {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : ZMod mersenne31Modulus)) :
    WordMemoryRouting w store := NativeWordMemoryFieldProofs.routing holds store mask

end Airbender.ReducedMachine.Native
