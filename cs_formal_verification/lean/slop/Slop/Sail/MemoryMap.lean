import Slop.Sail.PMA
import Human.Helpers.Core.Configuration

/-! The PMA check on Airbender's memory map (`Configuration.memoryMap`): loads anywhere, stores to RAM
(`2^22 ≤ address`), instruction fetches from ROM. -/

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail Configuration
open _root_.Sail.ArchSem

theorem memory_map_region {address : BitVec 32} {size : Nat}
    (width : size = 1 ∨ size = 2 ∨ size = 4) (aligned : address.toNat % size = 0) :
    SailRV32.Functions.matching_pma_region memoryMap (.Physaddr (address.setWidth 34)) size =
      some (if address.toNat < ROM_END then region 0 ROM_END true false true
        else region ROM_END (RAM_END - ROM_END) true true false) := by
  have bound := address.isLt
  by_cases rom : address.toNat < ROM_END
  all_goals
    simp only [ROM_END] at rom
    rcases width with rfl | rfl | rfl
    all_goals
      simp [rom, memoryMap, region, ROM_END, RAM_END, SailRV32.Functions.matching_pma_region,
        SailRV32.Functions.matching_pma_region_bits_range, SailRV32.Functions.range_subset,
        SailRV32.Functions.bits_of_physaddr, SailRV32.Functions.zero_extend,
        SailRV32.Functions.to_bits, SailRV32.Functions.zopz0zIzJ_u,
        _root_.Sail.BitVec.zeroExtend, _root_.Sail.BitVec.toNatInt, _root_.Sail.get_slice_int,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth]
      first | omega | (split_ifs <;> first | rfl | (exfalso; omega))

/-- Which aligned native accesses Airbender's memory map permits: loads anywhere (ROM below `2^22`, RAM
    above), stores to RAM, instruction fetches from ROM. -/
def MapPermits (address : BitVec 32) : SailRV32.MemoryAccessType SailRV32.mem_payload → Prop
  | .Load .Data => True
  | .Store .Data => ROM_END ≤ address.toNat
  | .InstructionFetch () => address.toNat < ROM_END
  | _ => False

theorem memory_map_access {before : State} {address : BitVec 32} {size : Nat}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (initialized : before.regs.get? .pma_regions = some memoryMap)
    (aligned : address.toNat % size = 0)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (ordinary : access = .Load .Data ∨ access = .Store .Data ∨ access = .InstructionFetch ())
    (permits : MapPermits address access) :
    run (SailRV32.Functions.pmaCheck (.Physaddr (address.setWidth 34)) size access .PBMT_PMA false)
      before = .ok (.Ok ⟨.CannotSplit, 0⟩) before := by
  simp only [SailRV32.Functions.pmaCheck, SailRV32.SailME.run]
  repeat rw [freeM_bind_assoc]
  rw [early_return_lift_bind, run_bind_of_ok _ _ _ _ _ (read_register initialized)]
  rw [memory_map_region width aligned]
  by_cases rom : address.toNat < ROM_END
  all_goals
    rcases ordinary with rfl | rfl | rfl
    all_goals simp only [MapPermits] at permits
    all_goals simp [rom, region, SailRV32.Functions.override_PMA, SailRV32.not, PreSail.assert,
      freeM_pure_bind]
    all_goals try (exfalso; omega)
    all_goals repeat first
      | rw [freeM_bind_assoc]
      | rw [early_return_lift_bind]
      | simp [freeM_pure_bind]
    all_goals rw [pma_aligned_memory width aligned _ _ (by simp)]
    all_goals rfl

end Airbender.Reference.RiscV.Sail
