import Slop.ISA.Equiv.MemVmem

/-! Sail's physical write path on Airbender: an aligned store of 1, 2 or 4 bytes to RAM announces the write
(`mem_write_ea`), then writes the bytes to Sail's memory (`writeBytes`); registers unchanged. One lemma per width. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000

theorem mem_write_ea_ram1 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 1 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 1 ≤ Airbender.RAM_END) :
    runSail (mem_write_ea (.Physaddr (zero_extend a)) 1 .Machine (.Store .Data) .PBMT_PMA false false false) σ =
      .ok (.Ok ()) σ := by
  have hw : (1 = 1 ∨ 1 = 2 ∨ 1 = 4) := by decide
  sail_run hs using mem_side with [pmp_check_machine, mmio_writable_false, pma_ram_store] stepwise
  rfl

theorem mem_write_value_ram1 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (v : BitVec 8)
    (ha : a.toNat % 1 = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 1 ≤ Airbender.RAM_END) :
    runSail (mem_write_value (.Physaddr (zero_extend a)) 1 v .Machine (.Store .Data) .PBMT_PMA false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem a.toNat 1 v } := by
  have hw : (1 = 1 ∨ 1 = 2 ∨ 1 = 4) := by decide
  sail_run hs using mem_side with [pmp_check_machine, mmio_writable_false, pma_ram_store] stepwise
  dsimp only [Sail.ArchSem.Mem_request.toArchSem]
  eval_closed
  simp only [phys_addr_toNat, setWidth_extract8, wroundtrip1]

theorem mem_write_ea_ram2 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 2 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 2 ≤ Airbender.RAM_END) :
    runSail (mem_write_ea (.Physaddr (zero_extend a)) 2 .Machine (.Store .Data) .PBMT_PMA false false false) σ =
      .ok (.Ok ()) σ := by
  have hw : (2 = 1 ∨ 2 = 2 ∨ 2 = 4) := by decide
  sail_run hs using mem_side with [pmp_check_machine, mmio_writable_false, pma_ram_store] stepwise
  rfl

theorem mem_write_value_ram2 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (v : BitVec 16)
    (ha : a.toNat % 2 = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 2 ≤ Airbender.RAM_END) :
    runSail (mem_write_value (.Physaddr (zero_extend a)) 2 v .Machine (.Store .Data) .PBMT_PMA false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem a.toNat 2 v } := by
  have hw : (2 = 1 ∨ 2 = 2 ∨ 2 = 4) := by decide
  sail_run hs using mem_side with [pmp_check_machine, mmio_writable_false, pma_ram_store] stepwise
  dsimp only [Sail.ArchSem.Mem_request.toArchSem]
  eval_closed
  simp only [phys_addr_toNat, setWidth_extract16, wroundtrip2]

theorem mem_write_ea_ram4 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 4 ≤ Airbender.RAM_END) :
    runSail (mem_write_ea (.Physaddr (zero_extend a)) 4 .Machine (.Store .Data) .PBMT_PMA false false false) σ =
      .ok (.Ok ()) σ := by
  have hw : (4 = 1 ∨ 4 = 2 ∨ 4 = 4) := by decide
  sail_run hs using mem_side with [pmp_check_machine, mmio_writable_false, pma_ram_store] stepwise
  rfl

theorem mem_write_value_ram4 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (v : BitVec 32)
    (ha : a.toNat % 4 = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 4 ≤ Airbender.RAM_END) :
    runSail (mem_write_value (.Physaddr (zero_extend a)) 4 v .Machine (.Store .Data) .PBMT_PMA false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem a.toNat 4 v } := by
  have hw : (4 = 1 ∨ 4 = 2 ∨ 4 = 4) := by decide
  sail_run hs using mem_side with [pmp_check_machine, mmio_writable_false, pma_ram_store] stepwise
  dsimp only [Sail.ArchSem.Mem_request.toArchSem]
  eval_closed
  simp only [phys_addr_toNat, setWidth_extract32, wroundtrip4]

theorem vmem_write_addr_ram1 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (v : BitVec 8)
    (ha : a.toNat % 1 = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 1 ≤ Airbender.RAM_END) :
    runSail (vmem_write_addr (.Virtaddr a) 1 v (.Store .Data) machineInfo false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem a.toNat 1 v } := by
  sail_run hs using mem_side with [satp_mode_machine, translate_store, mem_write_ea_ram1, mem_write_value_ram1]
    stepwise
  eval_closed
  simp only [Bool.and_self, setWidth_extract8]

theorem vmem_write1 (σ : SailState) (hs : Airbender.Configured σ) (r : BitVec 5) (off : BitVec 32) (v : BitVec 8)
    (ha : (xget σ r + off).toNat % 1 = 0) (h1 : Airbender.RAM_START ≤ (xget σ r + off).toNat)
    (h2 : (xget σ r + off).toNat + 1 ≤ Airbender.RAM_END) :
    runSail (vmem_write (.Regidx r) off 1 v (.Store .Data) false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem (xget σ r + off).toNat 1 v } := by
  sail_run hs using mem_side with [vmem_write_addr_ram1] stepwise
  rfl

theorem vmem_write_addr_ram2 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (v : BitVec 16)
    (ha : a.toNat % 2 = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 2 ≤ Airbender.RAM_END) :
    runSail (vmem_write_addr (.Virtaddr a) 2 v (.Store .Data) machineInfo false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem a.toNat 2 v } := by
  sail_run hs using mem_side with [satp_mode_machine, translate_store, mem_write_ea_ram2, mem_write_value_ram2]
    stepwise
  eval_closed
  simp only [Bool.and_self, setWidth_extract16]

theorem vmem_write2 (σ : SailState) (hs : Airbender.Configured σ) (r : BitVec 5) (off : BitVec 32) (v : BitVec 16)
    (ha : (xget σ r + off).toNat % 2 = 0) (h1 : Airbender.RAM_START ≤ (xget σ r + off).toNat)
    (h2 : (xget σ r + off).toNat + 2 ≤ Airbender.RAM_END) :
    runSail (vmem_write (.Regidx r) off 2 v (.Store .Data) false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem (xget σ r + off).toNat 2 v } := by
  sail_run hs using mem_side with [vmem_write_addr_ram2] stepwise
  rfl

theorem vmem_write_addr_ram4 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (v : BitVec 32)
    (ha : a.toNat % 4 = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 4 ≤ Airbender.RAM_END) :
    runSail (vmem_write_addr (.Virtaddr a) 4 v (.Store .Data) machineInfo false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem a.toNat 4 v } := by
  sail_run hs using mem_side with [satp_mode_machine, translate_store, mem_write_ea_ram4, mem_write_value_ram4]
    stepwise
  eval_closed
  simp only [Bool.and_self, setWidth_extract32]

theorem vmem_write4 (σ : SailState) (hs : Airbender.Configured σ) (r : BitVec 5) (off : BitVec 32) (v : BitVec 32)
    (ha : (xget σ r + off).toNat % 4 = 0) (h1 : Airbender.RAM_START ≤ (xget σ r + off).toNat)
    (h2 : (xget σ r + off).toNat + 4 ≤ Airbender.RAM_END) :
    runSail (vmem_write (.Regidx r) off 4 v (.Store .Data) false false false) σ =
      .ok (.Ok true) { σ with mem := writeBytes σ.mem (xget σ r + off).toNat 4 v } := by
  sail_run hs using mem_side with [vmem_write_addr_ram4] stepwise
  rfl

end Slop.Equiv
