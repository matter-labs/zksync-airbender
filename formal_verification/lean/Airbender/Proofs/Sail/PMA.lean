import Airbender.Proofs.Sail.PMP
import Airbender.Review.Helpers.Memory.Platform

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

theorem physical_address_value (address : BitVec 32) :
    (address.setWidth 34).toNat = address.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have bound := address.isLt; omega)

/-- The actual physical alignment predicate agrees with native RV32 byte
    alignment for every access width. -/
theorem physical_aligned {address : BitVec 32} {size : Nat}
    (aligned : address.toNat % size = 0) :
    SailRV32.Functions.is_aligned_paddr (.Physaddr (address.setWidth 34)) size = true := by
  simp only [SailRV32.Functions.is_aligned_paddr, _root_.Sail.BitVec.toNatInt]
  change (((address.toNat % size : Nat) : Int) == 0) = true
  rw [aligned]
  rfl

theorem physical_word_aligned {address : BitVec 32} (aligned : address.toNat % 4 = 0) :
    SailRV32.Functions.is_aligned_paddr (.Physaddr (address.setWidth 34)) 4 = true :=
  physical_aligned aligned

/-- An aligned byte, halfword or word fits in the initialized RV32 region,
    including the last native access of each width. -/
theorem rv32_memory_region {address : BitVec 32} {size : Nat}
    (width : size = 1 ∨ size = 2 ∨ size = 4) (aligned : address.toNat % size = 0)
    (attributes : SailRV32.PMA) :
    SailRV32.Functions.matching_pma_region [rv32Region attributes]
      (.Physaddr (address.setWidth 34)) size = some (rv32Region attributes) := by
  have bound := address.isLt
  have endBound : address.toNat + size ≤ 4294967296 := by
    rcases width with rfl | rfl | rfl <;> omega
  rcases width with rfl | rfl | rfl
  all_goals
    simp [SailRV32.Functions.matching_pma_region,
      SailRV32.Functions.matching_pma_region_bits_range, SailRV32.Functions.range_subset,
      rv32Region, SailRV32.Functions.bits_of_physaddr, SailRV32.Functions.zero_extend,
      SailRV32.Functions.to_bits, SailRV32.Functions.zopz0zIzJ_u,
      _root_.Sail.BitVec.zeroExtend, _root_.Sail.BitVec.toNatInt, _root_.Sail.get_slice_int,
      BitVec.toNat_add, BitVec.toNat_setWidth]
    omega

theorem rv32_word_region {address : BitVec 32} (aligned : address.toNat % 4 = 0)
    (attributes : SailRV32.PMA) :
    SailRV32.Functions.matching_pma_region [rv32Region attributes]
      (.Physaddr (address.setWidth 34)) 4 = some (rv32Region attributes) :=
  rv32_memory_region (Or.inr (Or.inr rfl)) aligned attributes

/-- Aligned ordinary native accesses need no splitting, independently of MAG attributes. -/
theorem pma_aligned_memory {address : BitVec 32} {size : Nat}
    (width : size = 1 ∨ size = 2 ∨ size = 4) (aligned : address.toNat % size = 0)
    (attributes : SailRV32.PMA) (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (ordinary : access = .Load .Data ∨ access = .Store .Data ∨ access = .InstructionFetch ()) :
    SailRV32.Functions.mag_pma_check attributes access (.Physaddr (address.setWidth 34)) size =
      pure (.Ok (.CannotSplit, 0)) := by
  rcases ordinary with rfl | rfl | rfl
  all_goals rcases width with rfl | rfl | rfl
  all_goals simp [SailRV32.Functions.mag_pma_check, SailRV32.Functions.is_mag_applicable_access,
    SailRV32.Functions.xlen_bytes, physical_aligned aligned, freeM_pure_bind]

theorem pma_aligned_word {address : BitVec 32} (aligned : address.toNat % 4 = 0)
    (attributes : SailRV32.PMA) (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (ordinary : access = .Load .Data ∨ access = .Store .Data ∨ access = .InstructionFetch ()) :
    SailRV32.Functions.mag_pma_check attributes access (.Physaddr (address.setWidth 34)) 4 =
      pure (.Ok (.CannotSplit, 0)) :=
  pma_aligned_memory (Or.inr (Or.inr rfl)) aligned attributes access ordinary

/-- The native PMA check follows from the initialized region and its permissions.
    It supplies no memory value or successful transfer premise. -/
theorem pma_memory_access {before : State} {address : BitVec 32} {attributes : SailRV32.PMA} {size : Nat}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (initialized : before.regs.get? .pma_regions = some [rv32Region attributes])
    (readable : attributes.readable = true) (writable : attributes.writable = true)
    (executable : attributes.executable = true) (aligned : address.toNat % size = 0)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (ordinary : access = .Load .Data ∨ access = .Store .Data ∨ access = .InstructionFetch ()) :
    run (SailRV32.Functions.pmaCheck (.Physaddr (address.setWidth 34)) size access .PBMT_PMA false)
      before = .ok (.Ok ⟨.CannotSplit, 0⟩) before := by
  simp only [SailRV32.Functions.pmaCheck, SailRV32.SailME.run]
  repeat rw [freeM_bind_assoc]
  rw [early_return_lift_bind, run_bind_of_ok _ _ _ _ _ (read_register initialized)]
  rw [rv32_memory_region width aligned]
  rcases ordinary with rfl | rfl | rfl
  all_goals simp [SailRV32.Functions.override_PMA, rv32Region, readable, writable, executable,
    SailRV32.not, PreSail.assert, freeM_pure_bind]
  all_goals repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | simp [freeM_pure_bind]
  all_goals rw [pma_aligned_memory width aligned attributes _ (by simp)]
  all_goals rfl

theorem pma_word_access {before : State} {address : BitVec 32} {attributes : SailRV32.PMA}
    (initialized : before.regs.get? .pma_regions = some [rv32Region attributes])
    (readable : attributes.readable = true) (writable : attributes.writable = true)
    (executable : attributes.executable = true) (aligned : address.toNat % 4 = 0)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (ordinary : access = .Load .Data ∨ access = .Store .Data ∨ access = .InstructionFetch ()) :
    run (SailRV32.Functions.pmaCheck (.Physaddr (address.setWidth 34)) 4 access .PBMT_PMA false)
      before = .ok (.Ok ⟨.CannotSplit, 0⟩) before :=
  pma_memory_access (Or.inr (Or.inr rfl)) initialized readable writable executable aligned access ordinary

end Airbender.Reference.RiscV.Sail
