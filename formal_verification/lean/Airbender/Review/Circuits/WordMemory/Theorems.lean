import Airbender.Review.Circuits.WordMemory.Model
import Airbender.Proofs.WordMemory.Transfers
import Airbender.Proofs.WordMemory.Address
import Airbender.Proofs.WordMemory.Shadow
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory

/-- Native v2 port selection, aligned address limbs, masked RAM/ROM loads and
    RAM-only stores. Public decoding, initialized history and Sail execution
    have separate interfaces; this statement is solely about native transfers. -/
theorem native_transfers (rom : Verification.WordROM) (w : Nat → ZMod mersenne31Modulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom) →
    NativeTransfers rom w :=
  Proofs.transfers (by decide)

/-- Native Mersenne31 address addition, including RV32 wraparound. Source and
    decoded-immediate bounds are explicit local inputs; initialized native-row
    assembly derives them from public decoding/history. -/
theorem native_address (rom : Verification.WordROM) (w : Nat → ZMod mersenne31Modulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom) →
    (sourceWord w).Bounded → (immediateWord w).Bounded →
    (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec :=
  Proofs.effective_address

/-- Every native RAM access below the four-MiB ROM boundary only refreshes its
    existing value. Full native matching still includes that access. This does
    not identify shadow values with architectural ROM bytes. -/
theorem native_shadow_refresh {rom : Verification.WordROM}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    {port : Trace.MemoryPort} (present : port ∈ importedConstraintsMemoryPorts)
    {address : BitVec 32} (region : address.toNat < 4194304)
    (same : port.address.code w = (Trace.Cell.ram address).addressCode) :
    port.writeCode w = port.readCode w :=
  Proofs.shadow_refresh (by decide) native present region same

end Airbender.WordMemory
