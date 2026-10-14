import Slop.Equiv.MemWrite

/-! Sail's `execute` = ours for stores: an aligned store of 1, 2 or 4 bytes to RAM writes the low bytes of `rs2`
to Sail's memory; registers unchanged. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem exec_store (σ : SailState) (hs : Airbender.Configured σ) (rs2 rs1 : BitVec 5) (x : BitVec 12) (n : Nat)
    (hn : n = 1 ∨ n = 2 ∨ n = 4) (ha : (xget σ rs1 + x.signExtend 32).toNat % n = 0)
    (h1 : Airbender.RAM_START ≤ (xget σ rs1 + x.signExtend 32).toNat)
    (h2 : (xget σ rs1 + x.signExtend 32).toNat + n ≤ Airbender.RAM_END) :
    runSail (Airbender.execute (Airbender.toSail (.store n rs2 rs1 (x.signExtend 32)))) σ =
      .ok RETIRE_SUCCESS
        { σ with mem := writeBytes σ.mem (xget σ rs1 + x.signExtend 32).toNat n ((xget σ rs2).setWidth (8 * n)) } := by
  simp only [Airbender.toSail, Airbender.execute, execute, execute_STORE, sext12]
  rcases hn with rfl | rfl | rfl
  · sail_run hs using mem_side with [vmem_write1] stepwise
    simp only [setWidth_extract_low8]
  · sail_run hs using mem_side with [vmem_write2] stepwise
    simp only [setWidth_extract_low16]
  · sail_run hs using mem_side with [vmem_write4] stepwise
    rw [extract_full32, BitVec.setWidth_eq]

end Slop.Equiv
