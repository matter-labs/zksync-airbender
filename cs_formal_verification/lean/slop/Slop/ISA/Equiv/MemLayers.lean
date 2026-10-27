import Slop.ISA.Equiv.MemLemmas
import Slop.ISA.Sail.KernelRfl

/-! Sail's memory path on Airbender, one layer per lemma (each its own small kernel check). Generic in the address
and the width (1, 2 or 4 bytes); only the region (ROM or RAM) and the alignment are hypotheses. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000

theorem pma_ram_load (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (ha : a.toNat % w = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + w ≤ Airbender.RAM_END) :
    runSail (pmaCheck (.Physaddr (zero_extend a)) w (.Load .Data) .PBMT_PMA false) σ =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) σ := by
  sail_run hs using mem_side
  rw [pma_regions_eq hs, match_ram a w (by omega) (by omega) h1 h2]
  sail_run hs using mem_side
  rfl

theorem pma_rom_load (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (ha : a.toNat % w = 0) (h2 : a.toNat + w ≤ Airbender.RAM_START) :
    runSail (pmaCheck (.Physaddr (zero_extend a)) w (.Load .Data) .PBMT_PMA false) σ =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) σ := by
  sail_run hs using mem_side
  rw [pma_regions_eq hs, match_rom a w (by omega) (by omega) h2]
  sail_run hs using mem_side
  rfl

theorem pma_ram_store (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (ha : a.toNat % w = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + w ≤ Airbender.RAM_END) :
    runSail (pmaCheck (.Physaddr (zero_extend a)) w (.Store .Data) .PBMT_PMA false) σ =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) σ := by
  sail_run hs using mem_side
  rw [pma_regions_eq hs, match_ram a w (by omega) (by omega) h1 h2]
  sail_run hs using mem_side
  rfl

theorem pma_rom_fetch (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (ha : a.toNat % w = 0) (h2 : a.toNat + w ≤ Airbender.RAM_START) :
    runSail (pmaCheck (.Physaddr (zero_extend a)) w (.InstructionFetch ()) .PBMT_PMA false) σ =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) σ := by
  sail_run hs using mem_side
  rw [pma_regions_eq hs, match_rom a w (by omega) (by omega) h2]
  sail_run hs using mem_side
  rfl

theorem physaddr_eq (a : BitVec 32) (h : a.toNat < 2 ^ 34) :
    (physaddr.Physaddr (BitVec.ofFin (w := 34) ⟨a.toNat, h⟩)) = .Physaddr (zero_extend a) := by
  congr 1

/-- Address translation in machine mode: the identity (any address). -/
theorem translate_load (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) :
    runSail (translateAddr (.Virtaddr a) (.Load .Data) .Machine) σ = .ok (.Ok (.Physaddr (zero_extend a), .PBMT_PMA, ())) σ := by
  have hlt : a.toNat < 2 ^ 34 := by have := a.isLt; omega
  rw [oracle_run hs _ (.Ok (.Physaddr (BitVec.ofFin (w := 34) ⟨a.toNat, hlt⟩), .PBMT_PMA, ())) (by kernel_rfl), physaddr_eq]

/-- Address translation in machine mode: the identity (any address). -/
theorem translate_store (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) :
    runSail (translateAddr (.Virtaddr a) (.Store .Data) .Machine) σ = .ok (.Ok (.Physaddr (zero_extend a), .PBMT_PMA, ())) σ := by
  have hlt : a.toNat < 2 ^ 34 := by have := a.isLt; omega
  rw [oracle_run hs _ (.Ok (.Physaddr (BitVec.ofFin (w := 34) ⟨a.toNat, hlt⟩), .PBMT_PMA, ())) (by kernel_rfl), physaddr_eq]

/-- Address translation in machine mode: the identity (any address). -/
theorem translate_fetch (σ : SailState) (hs : Airbender.Configured σ) (a : BitVec 32) :
    runSail (translateAddr (.Virtaddr a) (.InstructionFetch ()) .Machine) σ = .ok (.Ok (.Physaddr (zero_extend a), .PBMT_PMA, ())) σ := by
  have hlt : a.toNat < 2 ^ 34 := by have := a.isLt; omega
  rw [oracle_run hs _ (.Ok (.Physaddr (BitVec.ofFin (w := 34) ⟨a.toNat, hlt⟩), .PBMT_PMA, ())) (by kernel_rfl), physaddr_eq]

/-- Machine mode: no address translation (any Airbender state). -/
theorem satp_mode_machine (σ : SailState) (hs : Airbender.Configured σ) : runSail (satp_mode .Machine) σ = .ok .Bare σ :=
  oracle_run hs _ _ (by kernel_rfl)

/-- Machine mode, no PMP entry enabled: physical memory protection allows everything (any address, width, access). -/
theorem pmp_check_machine (σ : SailState) (hs : Airbender.Configured σ) (p : physaddr) (w : Nat)
    (acc : MemoryAccessType mem_payload) : runSail (pmpCheck p w acc .Machine) σ = .ok none σ :=
  oracle_run hs _ _ (by kernel_rfl)

/-- No memory-mapped devices (CLINT, HTIF, signature region) anywhere: every access goes to plain memory. -/
theorem mmio_writable_false (σ : SailState) (hs : Airbender.Configured σ) (p : physaddr) (w : Nat) :
    runSail (within_mmio_writable p w) σ = .ok false σ :=
  oracle_run hs _ _ (by kernel_rfl)

theorem mmio_readable_false (σ : SailState) (hs : Airbender.Configured σ) (p : physaddr) (w : Nat) :
    runSail (within_mmio_readable p w) σ = .ok false σ :=
  oracle_run hs _ _ (by kernel_rfl)

end Slop.Equiv
