import Slop.Equiv.MemRead

/-! `vmem_read_addr` on Airbender (machine mode, no translation, no split): an aligned load of 1, 2 or 4 bytes from
ROM or RAM returns the bytes in Sail's memory (`readBytes`), state unchanged. One lemma per (region, width). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000

/-- What `default_access_info` gives a load in machine mode. -/
abbrev machineInfo : AccessInfo := { eff_privilege := .Machine, pmlen := 0, as_guest := false }

theorem vmem_read_addr_ram1 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 1 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 1 ≤ Airbender.RAM_END) :
    runSail (vmem_read_addr (.Virtaddr a) 1 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 1)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_ram1] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_closed
  simp only [BitVec.setWidth_eq, update_full8]

theorem vmem_read_addr_ram2 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 2 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 2 ≤ Airbender.RAM_END) :
    runSail (vmem_read_addr (.Virtaddr a) 2 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 2)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_ram2] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_closed
  simp only [BitVec.setWidth_eq, update_full16]

theorem vmem_read_addr_ram4 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 4 ≤ Airbender.RAM_END) :
    runSail (vmem_read_addr (.Virtaddr a) 4 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 4)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_ram4] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_closed
  simp only [BitVec.setWidth_eq, update_full32]

theorem vmem_read_addr_rom1 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 1 = 0)
    (h2 : a.toNat + 1 ≤ Airbender.RAM_START) :
    runSail (vmem_read_addr (.Virtaddr a) 1 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 1)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_rom1] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_closed
  simp only [BitVec.setWidth_eq, update_full8]

theorem vmem_read_addr_rom2 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 2 = 0)
    (h2 : a.toNat + 2 ≤ Airbender.RAM_START) :
    runSail (vmem_read_addr (.Virtaddr a) 2 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 2)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_rom2] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_closed
  simp only [BitVec.setWidth_eq, update_full16]

theorem vmem_read_addr_rom4 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (h2 : a.toNat + 4 ≤ Airbender.RAM_START) :
    runSail (vmem_read_addr (.Virtaddr a) 4 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 4)) σ := by
  sail_run hs using mem_side with [satp_mode_machine, translate_load, mem_read_rom4] stepwise
  simp only [EStateM.Result.ok.injEq, Result.Ok.injEq, and_true]
  eval_closed
  simp only [BitVec.setWidth_eq, update_full32]

/-- Any aligned readable address (ROM or RAM: an aligned access never straddles the two). -/
theorem vmem_read_addr1 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 1 = 0)
    (hr : a.toNat + 1 ≤ Airbender.RAM_END) :
    runSail (vmem_read_addr (.Virtaddr a) 1 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 1)) σ := by
  by_cases h : Airbender.RAM_START ≤ a.toNat
  · exact vmem_read_addr_ram1 σ hs a ha h hr
  · exact vmem_read_addr_rom1 σ hs a ha (by simp only [Airbender.RAM_START, RV.ROM_END] at h ⊢; omega)

theorem vmem_read1 (σ : SailState) (hs : Airbender.Configured σ) (r : BitVec 5) (off : BitVec 32)
    (ha : (xget σ r + off).toNat % 1 = 0) (hr : (xget σ r + off).toNat + 1 ≤ Airbender.RAM_END) :
    runSail (vmem_read (.Regidx r) off 1 (.Load .Data) false false false) σ =
      .ok (.Ok (readBytes σ.mem (xget σ r + off).toNat 1)) σ := by
  sail_run hs using mem_side with [vmem_read_addr1] stepwise
  rfl

/-- Any aligned readable address (ROM or RAM: an aligned access never straddles the two). -/
theorem vmem_read_addr2 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 2 = 0)
    (hr : a.toNat + 2 ≤ Airbender.RAM_END) :
    runSail (vmem_read_addr (.Virtaddr a) 2 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 2)) σ := by
  by_cases h : Airbender.RAM_START ≤ a.toNat
  · exact vmem_read_addr_ram2 σ hs a ha h hr
  · exact vmem_read_addr_rom2 σ hs a ha (by simp only [Airbender.RAM_START, RV.ROM_END] at h ⊢; omega)

theorem vmem_read2 (σ : SailState) (hs : Airbender.Configured σ) (r : BitVec 5) (off : BitVec 32)
    (ha : (xget σ r + off).toNat % 2 = 0) (hr : (xget σ r + off).toNat + 2 ≤ Airbender.RAM_END) :
    runSail (vmem_read (.Regidx r) off 2 (.Load .Data) false false false) σ =
      .ok (.Ok (readBytes σ.mem (xget σ r + off).toNat 2)) σ := by
  sail_run hs using mem_side with [vmem_read_addr2] stepwise
  rfl

/-- Any aligned readable address (ROM or RAM: an aligned access never straddles the two). -/
theorem vmem_read_addr4 (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (hr : a.toNat + 4 ≤ Airbender.RAM_END) :
    runSail (vmem_read_addr (.Virtaddr a) 4 (.Load .Data) machineInfo false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 4)) σ := by
  by_cases h : Airbender.RAM_START ≤ a.toNat
  · exact vmem_read_addr_ram4 σ hs a ha h hr
  · exact vmem_read_addr_rom4 σ hs a ha (by simp only [Airbender.RAM_START, RV.ROM_END] at h ⊢; omega)

theorem vmem_read4 (σ : SailState) (hs : Airbender.Configured σ) (r : BitVec 5) (off : BitVec 32)
    (ha : (xget σ r + off).toNat % 4 = 0) (hr : (xget σ r + off).toNat + 4 ≤ Airbender.RAM_END) :
    runSail (vmem_read (.Regidx r) off 4 (.Load .Data) false false false) σ =
      .ok (.Ok (readBytes σ.mem (xget σ r + off).toNat 4)) σ := by
  sail_run hs using mem_side with [vmem_read_addr4] stepwise
  rfl

end Slop.Equiv
