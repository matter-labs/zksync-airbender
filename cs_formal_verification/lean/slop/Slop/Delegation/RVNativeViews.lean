module
public import Slop.Delegation.NativeViews
public import Slop.Trace.RVCells
public import Human.Helpers.Memory.RowEvents

@[expose] public section

/-! RV twins of `NativeViews.lean`: the word an `RV.State`'s RAM holds at an address (RAM at any address, the shadow RAM
    below `ROM_END` included), and what a native indirect port's read/write says about it. -/

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true

/-- The encoded word of the RV RAM at `address`. -/
def rvRamEncoding (state : RV.State) (address : BitVec 32) : Word :=
  Word.ofBitVec (RV.read state.mem address 4)

/-- `n` RV RAM words from `pointer + 4 * offset`. -/
def rvBlockWords (state : RV.State) (pointer : BitVec 32) (n offset : Nat) : Vector Word n :=
  Vector.ofFn fun i => rvRamEncoding state (pointer + BitVec.ofNat 32 (4 * (offset + i.val)))

theorem rv_ram_read {state : RV.State} {address value : BitVec 32}
    (read : (Cell.ram address).readRV state = some value) : RV.read state.mem address 4 = value := by
  rw [readRV_ram state (readable_of_readRV read)] at read
  exact Option.some.inj read

theorem rv_ram_encoding_read {state : RV.State} {address value : BitVec 32}
    (read : (Cell.ram address).readRV state = some value) : rvRamEncoding state address = Word.ofBitVec value := by
  rw [rvRamEncoding, rv_ram_read read]

theorem rv_ram_encoding_native {state : RV.State} {address : BitVec 32} {word : Word}
    (bound : word.Bounded) (read : (Cell.ram address).readRV state = some word.toBitVec) :
    rvRamEncoding state address = word := by
  rw [rv_ram_encoding_read read]
  exact Word.eq_of_value (Word.ofBitVec_bound _) bound (by rw [Word.ofBitVec_value, Word.toBitVec_toNat bound])

/-- The aligned RAM cell reads its encoding. -/
theorem rv_encoded_read {state : RV.State} {address : BitVec 32} (aligned : (Cell.ram address).Aligned) :
    (Cell.ram address).readRV state = some (rvRamEncoding state address).toBitVec := by
  rw [readRV_ram state (readable_of_aligned aligned), rvRamEncoding, Word.ofBitVec_roundtrip]

theorem rv_indirect_word_observations {p : Nat} {w : Nat → ZMod p}
    {port : MemoryPort} {indirect : Verification.IndirectPort} {before after : RV.State}
    (shape : port.address = .indirect indirect)
    (reads : (readToken w port).word.Bounded)
    (writes : (Arithmetic.Word.mk (Nat.unpair (port.writeCode w)).1
      (Nat.unpair (port.writeCode w)).2).Bounded)
    (observed : ∃ cell : Cell, cell.addressCode = port.address.code w ∧
      cell.readRV before = some (memoryWord (port.readCode w)) ∧
      cell.readRV after = some (memoryWord (port.writeCode w))) :
    rvRamEncoding before (indirect.address w) = (readToken w port).word ∧
      rvRamEncoding after (indirect.address w) =
        Arithmetic.Word.mk (Nat.unpair (port.writeCode w)).1 (Nat.unpair (port.writeCode w)).2 := by
  obtain ⟨cell, code, read, written⟩ := observed
  rw [shape] at code
  have same := indirect_cell code
  subst cell
  exact ⟨rv_ram_encoding_native reads read, rv_ram_encoding_native writes written⟩

end Airbender.Delegation.Proofs
