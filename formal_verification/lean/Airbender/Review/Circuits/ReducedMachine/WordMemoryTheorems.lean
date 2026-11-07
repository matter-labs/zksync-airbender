import Airbender.Proofs.ReducedMachine.NativeWordMemoryAccess

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false

/-- Accepted actual native equations derive word-only operand/port-space routing.
    Decoded mask stays explicit; original memory, ROM and execution stay separate. -/
theorem word_memory_routing {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : ZMod mersenne31Modulus)) :
    WordMemoryRouting w store := NativeWordMemoryFieldProofs.routing holds store mask

/-- The actual load retains its memory shadow address and selects ROM/RAM
    words before architectural destination masking. Numerical table meaning
    and original Sail reads remain separate. -/
theorem word_load_access {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus)) :
    WordLoadAccess w := NativeWordMemoryAccessProofs.load_access holds mask

/-- The actual store writes its second source to memory without rd-zero masking. -/
theorem word_store_access {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus)) :
    WordStoreAccess w := NativeWordMemoryAccessProofs.store_access holds mask

end Airbender.ReducedMachine.Native
