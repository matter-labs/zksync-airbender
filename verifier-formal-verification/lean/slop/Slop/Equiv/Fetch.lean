import Slop.Equiv.ExecStore

/-! Sail's `fetch` on Airbender: at a 4-byte aligned PC in ROM, holding a 32-bit (non-compressed) instruction,
fetch returns the 4 bytes at PC; state unchanged. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem mem_read_fetch_rom4 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (h2 : a.toNat + 4 ≤ Airbender.RAM_START) :
    runF (mem_read (.InstructionFetch ()) .PBMT_PMA .Machine (.Physaddr (zero_extend a)) 4 false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 4)) σ := by
  have hw : (4 = 1 ∨ 4 = 2 ∨ 4 = 4) := by decide
  sail_run hs using mem_side with [pmp_check_machine, mmio_readable_false, pma_rom_fetch] stepwise
  dsimp only [Sail.ArchSem.Mem_request.toArchSem, MemoryOpResult_drop_meta]
  eval_closed
  simp only [EStateM.Result.ok.injEq, and_true, Result.Ok.injEq, phys_addr_toNat, roundtrip4, BitVec.setWidth_eq, update_full32]

theorem access_low (a : BitVec 32) (h : a.toNat % 4 = 0) : BitVec.access a 0 = 0#1 ∧ BitVec.access a 1 = 0#1 := by
  have h0 : a.toNat.testBit 0 = false := by simp [Nat.testBit_zero]; omega
  have h1 : a.toNat.testBit 1 = false := by
    rw [show (1 : Nat) = 0 + 1 from rfl, Nat.testBit_succ, Nat.testBit_zero]; simp; omega
  rw [BitVec.testBit_toNat] at h0 h1
  simp [BitVec.access, BitVec.getLsbD_eq_getElem] at h0 h1 ⊢
  simp [h0, h1]

theorem fetch_rom (σ : FState) (hs : Airbender.Sys σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START)
    (hrvc : isRVC (Sail.BitVec.extractLsb (readBytes σ.mem (σ.regs .PC).toNat 4) 15 0) = false) :
    runF (fetch ()) σ = .ok (.F_Base (readBytes σ.mem (σ.regs .PC).toNat 4)) σ := by
  have ⟨hb0, hb1⟩ := access_low _ ha
  sail_run hs using mem_side with [translate_fetch, mem_read_fetch_rom4] stepwise
  eval_closed
  simp only [BitVec.setWidth_eq]

end Slop.Equiv
