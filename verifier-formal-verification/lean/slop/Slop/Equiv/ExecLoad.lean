import Slop.Equiv.MemVmem

/-! Sail's `execute` = ours for loads: an aligned readable load of 1, 2 or 4 bytes writes the (sign- or zero-)
extended bytes to `rd`; a load into x0 does nothing (Airbender). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem regidx_beq_zreg (rd : BitVec 5) (h : rd ≠ 0) : (regidx.Regidx rd == zreg) = false := by
  show (rd == 0#5) = false
  simpa using h

theorem exec_load_x0 (σ : SailState) (rs1 : BitVec 5) (off : BitVec 32) (n : Nat) (sg : Bool) :
    runSail (Airbender.execute (Airbender.toSail (.load n sg 0 rs1 off))) σ = .ok RETIRE_SUCCESS σ := rfl

theorem exec_load (σ : SailState) (hs : Airbender.Configured σ) (rd rs1 : BitVec 5) (x : BitVec 12) (n : Nat) (sg : Bool)
    (hn : n = 1 ∨ n = 2 ∨ n = 4) (hrd : rd ≠ 0) (ha : (xget σ rs1 + x.signExtend 32).toNat % n = 0)
    (hr : (xget σ rs1 + x.signExtend 32).toNat + n ≤ Airbender.RAM_END) :
    runSail (Airbender.execute (Airbender.toSail (.load n sg rd rs1 (x.signExtend 32)))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (extend_value (!sg) (readBytes σ.mem (xget σ rs1 + x.signExtend 32).toNat n))) := by
  simp only [Airbender.toSail, Airbender.execute, regidx_beq_zreg rd hrd, Bool.false_eq_true, ite_false, execute,
    execute_LOAD, sext12]
  rcases hn with rfl | rfl | rfl
  · sail_run hs using mem_side with [vmem_read1] stepwise; rfl
  · sail_run hs using mem_side with [vmem_read2] stepwise; rfl
  · sail_run hs using mem_side with [vmem_read4] stepwise; rfl

end Slop.Equiv
