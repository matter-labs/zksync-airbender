module
public import Human.Helpers.Context.RVRowContext
public import Proven.ISA.RV.Mem

@[expose] public section

/-! RV-state laws for the public cells: the RV siblings of `SailCells.lean`. Each law is about one `Cell.readRV` /
    `Cell.writeRV` step on an `RV.State`. Register reads are `getReg` (x0 reads 0), register writes are `setReg`
    (x0's stored value is never visible), RAM reads and stores are `RV.read` / `RV.store` on the byte memory. -/

namespace Airbender.Trace.Proofs
open Airbender.Trace

theorem readRV_register (index : BitVec 5) (before : RV.State) :
    (Cell.register index).readRV before = some (before.getReg index) := by rfl

theorem readRV_ram {address : BitVec 32} (before : RV.State) (readable : RV.readable address 4) :
    (Cell.ram address).readRV before = some (RV.read before.mem address 4) := by
  simp [Cell.readRV, readable]

theorem writeRV_register (index : BitVec 5) (value : BitVec 32) (before : RV.State) :
    (Cell.register index).writeRV value before = some (before.setReg index value) := by rfl

theorem writeRV_ram {address : BitVec 32} (value : BitVec 32) (before : RV.State) :
    (Cell.ram address).writeRV value before = some (before.store address value 4) := by rfl

theorem getReg_setReg_same (before : RV.State) (index : BitVec 5) (value : BitVec 32) :
    (before.setReg index value).getReg index = if index = 0 then 0 else value := by
  simp [RV.State.getReg, RV.State.setReg]

theorem getReg_setReg_other (before : RV.State) {index other : BitVec 5} (different : other ≠ index)
    (value : BitVec 32) : (before.setReg index value).getReg other = before.getReg other := by
  simp [RV.State.getReg, RV.State.setReg, different]

theorem getReg_store (before : RV.State) (address value : BitVec 32) (index : BitVec 5) :
    (before.store address value 4).getReg index = before.getReg index := by rfl

/-- An aligned RAM cell lies in the readable range (the word fits below `2^32`). -/
theorem readable_of_aligned {address : BitVec 32} (aligned : (Cell.ram address).Aligned) :
    RV.readable address 4 := by
  have small := address.isLt
  have alignedAddress : address.toNat % 4 = 0 := aligned
  simp only [RV.readable, RV.RAM_END]
  omega

/-- A RAM read that succeeds lies in the readable range. -/
theorem readable_of_readRV {address : BitVec 32} {before : RV.State} {old : BitVec 32}
    (read : (Cell.ram address).readRV before = some old) : RV.readable address 4 := by
  by_contra h
  simp [Cell.readRV, h] at read

/-- Reading a tracked cell back after writing it gives the value written. The `zero` hypothesis is the x0 law: a
    write to `x0` is never visible, so only the zero value reads back. A RAM write always succeeds (RAM at any
    address); the cell's alignment keeps the word readable. -/
theorem writeRV_readback (cell : Cell) (value : BitVec 32) (before : RV.State)
    (zero : cell = .register 0 → value = 0) (aligned : cell.Aligned) :
    ∃ after, cell.writeRV value before = some after ∧ cell.readRV after = some value := by
  cases cell with
  | register index =>
    refine ⟨before.setReg index value, writeRV_register index value before, ?_⟩
    rw [readRV_register, getReg_setReg_same]
    by_cases zeroIndex : index = 0
    · rw [ite_eq_left zeroIndex, zero (by rw [zeroIndex])]
    · rw [ite_eq_right zeroIndex]
  | ram address =>
    refine ⟨before.store address value 4, writeRV_ram value before, ?_⟩
    rw [readRV_ram _ (readable_of_aligned aligned)]
    exact congrArg some (RV.read_write_same4 before.mem address value)

/-- A write leaves every other aligned cell's RV read unchanged. Register aliases are handled by `setReg`,
    RAM windows by byte disjointness (both cells are aligned and different). -/
theorem writeRV_frame {before after : RV.State} {cell other : Cell} {value old : BitVec 32}
    (written : cell.writeRV value before = some after) (different : other ≠ cell)
    (aligned : cell.Aligned) (otherAligned : other.Aligned)
    (read : other.readRV before = some old) : other.readRV after = some old := by
  cases cell with
  | register index =>
    have same : before.setReg index value = after := Option.some.inj ((writeRV_register index value before).symm.trans written)
    subst same
    cases other with
    | register reader =>
      have distinct : reader ≠ index := fun equal => different (by rw [equal])
      rw [readRV_register] at read ⊢
      rw [getReg_setReg_other _ distinct]
      exact read
    | ram address =>
      have readable := readable_of_readRV read
      rw [readRV_ram _ readable] at read ⊢
      exact read
  | ram address =>
    have same : before.store address value 4 = after := Option.some.inj ((writeRV_ram value before).symm.trans written)
    subst same
    cases other with
    | register reader =>
      rw [readRV_register] at read ⊢
      rw [getReg_store]
      exact read
    | ram reader =>
      have distinct : reader ≠ address := fun equal => different (by rw [equal])
      have distinctNat : reader.toNat ≠ address.toNat := fun equal => distinct (BitVec.eq_of_toNat_eq equal)
      have readable := readable_of_readRV read
      have alignedAddress : address.toNat % 4 = 0 := aligned
      have alignedReader : reader.toNat % 4 = 0 := otherAligned
      have writableBounds := readable_of_aligned aligned
      have readableBounds := readable
      have disjoint : address.toNat + 4 ≤ reader.toNat ∨ reader.toNat + 4 ≤ address.toNat := by omega
      rw [readRV_ram _ readable] at read ⊢
      have bytes := RV.read_write_disjoint before.mem address value reader 4 4 disjoint
        (by omega) (by omega)
      exact congrArg some (bytes.trans (Option.some.inj read))

/-- Writes to RAM never change the PC or the input stream: only the register file or byte memory moves. -/
theorem writeRV_pc {before after : RV.State} {cell : Cell} {value : BitVec 32}
    (written : cell.writeRV value before = some after) : after.pc = before.pc ∧ after.input = before.input := by
  cases cell <;> (obtain rfl := Option.some.inj written; exact ⟨rfl, rfl⟩)

/-- Cell writes never change the ROM image. -/
theorem writeRV_rom {before after : RV.State} {cell : Cell} {value : BitVec 32}
    (written : cell.writeRV value before = some after) : after.rom = before.rom := by
  cases cell <;> (obtain rfl := Option.some.inj written; rfl)

/-- `RV.Same` states agree on every RV cell read. -/
theorem readRV_congr_same {cell : Cell} {left right : RV.State} (same : RV.Same left right) :
    cell.readRV left = cell.readRV right := by
  obtain ⟨_, regs, _, mem, _⟩ := same
  cases cell with
  | register index => simp only [readRV_register, regs index]
  | ram address => simp only [Cell.readRV, mem]

/-- Writing back the value a register cell holds leaves the RV state the same (`RV.Same`), even though `x0`'s
    stored value may change: its read is always 0. -/
theorem writeRV_self_same_register {before after : RV.State} {index : BitVec 5} {value : BitVec 32}
    (read : (Cell.register index).readRV before = some value)
    (written : (Cell.register index).writeRV value before = some after) : RV.Same after before := by
  have same : before.setReg index value = after :=
    Option.some.inj ((writeRV_register index value before).symm.trans written)
  have getEq : before.getReg index = value := Option.some.inj ((readRV_register index before).symm.trans read)
  subst same
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro j
  by_cases different : j = index
  · subst different
    rw [getReg_setReg_same]
    by_cases zeroIndex : j = 0
    · simp [zeroIndex, RV.State.getReg]
    · rw [ite_eq_right zeroIndex, getEq]
  · exact getReg_setReg_other before different value

end Airbender.Trace.Proofs
