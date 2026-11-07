import Airbender.Proofs.Blake2Worker.NativeMemory

namespace Airbender.Blake2Worker.Native
open Verification

/-- Complete local native acceptance derives canonical pointer alignment and all43
    ABI-bound Boolean borrows/difference bounds. Initialized reads, raw clocks,
    matching, processing/issuance and protocol accounting remain separate. -/
theorem local_memory_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table)) : LocalMemoryEffects w := by
  exact MemoryProofs.local_effects holds

end Airbender.Blake2Worker.Native
