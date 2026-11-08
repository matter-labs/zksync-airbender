module
public import Slop.Trace.RVWritable
public import Slop.SubwordMemory

@[expose] public section

namespace Airbender.Trace.RVWritable
open Arithmetic Trace.Proofs

/-- A subword store-port write into RAM lands at ROM_END or above. -/
theorem subword_store_ram_writable {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    (setup : Table (ZMod p) (fields 9)) (w : Nat → ZMod p)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (SubwordMemory.importedConstraints setup))
    (index : BitVec 32)
    (same : (SubwordMemory.importedConstraintsMemoryPorts[2]).address.code w = (Cell.ram index).addressCode) :
    RV.ROM_END ≤ index.toNat := by
  have tagged : Nat.pair (w 10).val (Nat.pair (w 27).val (w 28).val) = (Cell.ram index).addressCode := by
    simpa [SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode] using same
  obtain ⟨tagEq, loEq, hiEq⟩ := ram_code_limbs index _ (w 27) (w 28) tagged
  have store : w 10 = 1 := by
    have h10 := (ZMod.natCast_zmod_val (w 10)).symm
    rw [tagEq] at h10
    simpa using h10
  have bounded : (Word.ofBitVec index).Bounded := by
    unfold Word.Bounded Word.ofBitVec
    dsimp [limbBase]
    have small := index.isLt
    omega
  have classified := SubwordMemory.Proofs.rom_selection (by omega) true constraints
    (by simpa using store) (address := Word.ofBitVec index)
    (by rw [← hiEq]; exact (ZMod.natCast_zmod_val _).symm) bounded
  exact ram_index_rom_bound index (classified.2 rfl)

end Airbender.Trace.RVWritable
