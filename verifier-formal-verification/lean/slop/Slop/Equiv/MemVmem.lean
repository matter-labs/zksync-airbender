import Slop.Equiv.MemRead

/-! `vmem_read_addr` on Airbender (machine mode, no translation, no split): an aligned load of 1, 2 or 4 bytes from
ROM or RAM returns the bytes in Sail's memory (`readBytes`), state unchanged. One lemma per (region, width). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- What `default_access_info` gives a load in machine mode. -/
abbrev machineInfo : AccessInfo := { eff_privilege := .Machine, pmlen := 0, as_guest := false }

theorem vmem_read_addr_ram1 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 1 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 1 ≤ Airbender.RAM_END) :
    runF (vmem_read_addr (.Virtaddr a) 1 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 1)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_ram1] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_nat
  simp only [BitVec.setWidth_eq, update_full8]

theorem vmem_read_addr_ram2 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 2 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 2 ≤ Airbender.RAM_END) :
    runF (vmem_read_addr (.Virtaddr a) 2 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 2)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_ram2] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_nat
  simp only [BitVec.setWidth_eq, update_full16]

theorem vmem_read_addr_ram4 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 4 ≤ Airbender.RAM_END) :
    runF (vmem_read_addr (.Virtaddr a) 4 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 4)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_ram4] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_nat
  simp only [BitVec.setWidth_eq, update_full32]

theorem vmem_read_addr_rom1 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 1 = 0)
    (h2 : a.toNat + 1 ≤ Airbender.RAM_START) :
    runF (vmem_read_addr (.Virtaddr a) 1 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 1)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_rom1] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_nat
  simp only [BitVec.setWidth_eq, update_full8]

theorem vmem_read_addr_rom2 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 2 = 0)
    (h2 : a.toNat + 2 ≤ Airbender.RAM_START) :
    runF (vmem_read_addr (.Virtaddr a) 2 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 2)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_rom2] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_nat
  simp only [BitVec.setWidth_eq, update_full16]

theorem vmem_read_addr_rom4 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (h2 : a.toNat + 4 ≤ Airbender.RAM_START) :
    runF (vmem_read_addr (.Virtaddr a) 4 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 4)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_rom4] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_nat
  simp only [BitVec.setWidth_eq, update_full32]

end Slop.Equiv
