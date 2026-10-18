import Airbender.Review.Helpers.Memory.BytePadding
import Airbender.Proofs.Sail.WordMemoryState
import Airbender.Proofs.Sail.CheckedMemory
import Airbender.Review.Helpers.Memory.Initialization

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail Trace

/-- Actual finite byte inserts have exact lookup behavior, including missing
    bytes outside the interval. The proof is symbolic in its extent. -/
theorem zero_byte_lookup (memory : Std.ExtHashMap Nat (BitVec 8)) (start count key : Nat) :
    (zeroByteMemory memory start count)[key]? =
      if start ≤ key ∧ key < start + count then some 0 else memory[key]? := by
  induction count with
  | zero => simp [zeroByteMemory]
  | succ count ih =>
    simp only [zeroByteMemory, Std.ExtHashMap.getElem?_insert, ih]
    by_cases last : start + count = key
    · subst key
      simp
    · simp only [beq_iff_eq, if_neg last]
      split_ifs <;> simp_all <;> omega

/-- Full ROM padding retains registers and every byte outside its actual tail. -/
theorem padded_rom_byte (before : State) (words key : Nat) (bound : words ≤ 1048576) :
    (paddedROMState before words).mem[key]? =
      if 4 * words ≤ key ∧ key < 4194304 then some 0 else before.mem[key]? := by
  unfold paddedROMState
  rw [zero_byte_lookup]
  have extent : 4 * words + (4194304 - 4 * words) = 4194304 := by omega
  rw [extent]

/-- Actual native word reads in the padded tail return zero. No expected byte
    or successful-read premise is supplied. -/
theorem padded_rom_zero_read (before : State) {words : Nat} (bound : words ≤ 1048576)
    {address : BitVec 32} (lower : 4 * words ≤ address.toNat)
    (upper : address.toNat + 4 ≤ 4194304) :
    (Cell.ram address).read (paddedROMState before words) = .ok 0 (paddedROMState before words) := by
  apply read_word_of_bytes
  intro i
  rw [padded_rom_byte before words _ bound, if_pos (by have := i.isLt; omega)]
  simp

/-- Successful reads entirely below or above the padding interval survive. -/
theorem padded_rom_word_frame {before : State} {words : Nat} (bound : words ≤ 1048576)
    {address : BitVec 32} {value : BitVec 32}
    (outside : address.toNat + 4 ≤ 4 * words ∨ 4194304 ≤ address.toNat)
    (read : (Cell.ram address).read before = .ok value before) :
    (Cell.ram address).read (paddedROMState before words) = .ok value (paddedROMState before words) := by
  apply read_word_of_bytes
  intro i
  rw [padded_rom_byte before words _ bound, if_neg (by have := i.isLt; omega)]
  exact read_word_memory read i

/-- Padding changes no public Machine/PMP/PMA configuration register. -/
theorem padded_rom_configuration {before : State} (configuration : FlatMemoryConfiguration before) (words : Nat) :
    FlatMemoryConfiguration (paddedROMState before words) :=
  configuration_register_frame (before := before) (after := paddedROMState before words) rfl configuration

/-- The original zero-boot profile survives explicit padding. Registers/PC are
    unchanged and architectural RAM lies beyond the padded ROM interval. -/
theorem padded_rom_initial_profile {before : State} {cells : List Cell}
    (profile : InitialProfile before cells) {words : Nat} (bound : words ≤ 1048576) :
    InitialProfile (paddedROMState before words) cells := by
  constructor
  · have pc := profile.pc
    change Reference.Sail.run (SailRV32.readReg .PC) before = .ok 0 before at pc
    change Reference.Sail.run (SailRV32.readReg .PC) _ = .ok 0 _
    apply read_register
    exact (read_register_iff (state := before)).mp pc
  · intro index
    exact rX_register_frame (before := before) (after := paddedROMState before words)
      rfl index (profile.registers index)
  · intro address member outside
    exact padded_rom_word_frame bound (Or.inr outside) (profile.ram address member outside)

end Airbender.Reference.RiscV.Sail
