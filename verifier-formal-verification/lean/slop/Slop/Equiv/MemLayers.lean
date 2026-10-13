import Slop.Equiv.MemLemmas

/-! Sail's memory path on Airbender, one layer per lemma (each its own small kernel check). Generic in the address
and the width (1, 2 or 4 bytes); only the region (ROM or RAM) and the alignment are hypotheses. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem pma_ram_load (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (ha : a.toNat % w = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + w ≤ Airbender.RAM_END) :
    runF (pmaCheck (.Physaddr (zero_extend a)) w (.Load .Data) .PBMT_PMA false) σ =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) σ := by
  sail_run hs using mem_side
  rw [pma_regions_eq hs, match_ram a w (by omega) (by omega) h1 h2]
  sail_run hs using mem_side
  rfl

theorem pma_rom_load (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (ha : a.toNat % w = 0) (h2 : a.toNat + w ≤ Airbender.RAM_START) :
    runF (pmaCheck (.Physaddr (zero_extend a)) w (.Load .Data) .PBMT_PMA false) σ =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) σ := by
  sail_run hs using mem_side
  rw [pma_regions_eq hs, match_rom a w (by omega) (by omega) h2]
  sail_run hs using mem_side
  rfl

theorem pma_ram_store (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (ha : a.toNat % w = 0) (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + w ≤ Airbender.RAM_END) :
    runF (pmaCheck (.Physaddr (zero_extend a)) w (.Store .Data) .PBMT_PMA false) σ =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) σ := by
  sail_run hs using mem_side
  rw [pma_regions_eq hs, match_ram a w (by omega) (by omega) h1 h2]
  sail_run hs using mem_side
  rfl

theorem pma_rom_fetch (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (ha : a.toNat % w = 0) (h2 : a.toNat + w ≤ Airbender.RAM_START) :
    runF (pmaCheck (.Physaddr (zero_extend a)) w (.InstructionFetch ()) .PBMT_PMA false) σ =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) σ := by
  sail_run hs using mem_side
  rw [pma_regions_eq hs, match_rom a w (by omega) (by omega) h2]
  sail_run hs using mem_side
  rfl

end Slop.Equiv
