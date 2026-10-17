import Airbender.Review.Helpers.Memory.InitialImage
import Airbender.Proofs.WordMemory.Transfers

namespace Airbender.WordMemory.Proofs
open Trace Arithmetic Verification

/-- Native RAM accesses below the ROM boundary can only refresh a value.
    The mixed final port writes either a register or RAM above that boundary. -/
theorem shadow_refresh {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    {port : MemoryPort} (present : port ∈ importedConstraintsMemoryPorts) {address : BitVec 32}
    (region : address.toNat < 4194304)
    (same : port.address.code w = (Cell.ram address).addressCode) :
    port.writeCode w = port.readCode w := by
  simp [importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · rfl
  · rfl
  · have effects := transfers hp native
    rcases effects.storeBit with load | store
    · change w 12 = 0 at load
      have space : w 32 = 1 := by simpa only [load, sub_zero] using effects.writeAddress.1
      simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair, space] at same
    · change w 12 = 1 at store
      have space : w 32 = 0 := by simpa only [store, sub_self] using effects.writeAddress.1
      have high : w 34 = w 20 := by simpa only [store, one_mul] using effects.writeAddress.2.2
      have oneNat : ((1 : Nat) : ZMod p).val = 1 :=
        ZMod.val_natCast_of_lt (show 1 < p from by omega)
      have one : (1 : ZMod p).val = 1 := by simpa only [Nat.cast_one] using oneNat
      have limbs : (w 33).val = (Word.ofBitVec address).lo ∧
          (w 34).val = (Word.ofBitVec address).hi := by
        simpa [MemoryAddress.code, pairCode, Cell.addressCode, Nat.pair_eq_pair, space, one] using same
      have below : (w 20).val < 64 := by
        rw [← high, limbs.2]
        change address.toNat / 65536 < 64
        omega
      have outside := (effects.store store).1
      omega

end Airbender.WordMemory.Proofs
