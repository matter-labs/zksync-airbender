import Slop.Equiv.Fetch

/-! One step of the Airbender machine, given what `execute` does: fetch from ROM, decode with our table,
`nextPC := PC + 4`, execute, check alignment, `PC := nextPC`. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Every opcode in our table ends in `11`. -/
theorem decode_opc {w : BitVec 32} {i : RV.Instr} (h : RV.decode w = some i) : (w.extractLsb' 0 7).toNat % 4 = 3 := by
  unfold RV.decode at h
  simp only at h
  split at h <;> first | (simp at h; done) | omega

/-- So Sail's fetch never sees a compressed instruction. -/
theorem decode_not_rvc {w : BitVec 32} {i : RV.Instr} (h : RV.decode w = some i) :
    isRVC (Sail.BitVec.extractLsb w 15 0) = false := by
  have h3 := decode_opc h
  simp only [isRVC, Sail.BitVec.extractLsb, SailRV32.not, Bool.not_eq_false', beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.extractLsb_toNat] at h3 ⊢
  omega

theorem step_of_exec (σ : SailState) (hs : Airbender.Configured σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (i : RV.Instr)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some i) (σ2 : SailState)
    (hexec : runSail (Airbender.execute (Airbender.toSail i)) (σ.set .nextPC (σ.regs .PC + 4)) = .ok RETIRE_SUCCESS σ2)
    (hal : (σ2.regs .nextPC).toNat % 4 = 0) :
    Airbender.step σ = some (σ2.set .PC (σ2.regs .nextPC)) := by
  have hf := fetch_rom σ hs ha h2 (decode_not_rvc hdec)
  unfold Airbender.step
  simp only [Slop.runF_bind, hf, Airbender.decode, hdec, Option.map_some, Slop.runF_writeReg]
  rw [Slop.runF_readReg]
  simp only [hexec, RETIRE_SUCCESS]
  rw [Slop.runF_bind, Slop.runF_readReg]
  simp only [hal, ne_eq, not_true_eq_false, ite_false, tick_pc, Slop.runF_bind, Slop.runF_writeReg, Slop.runF_pure]
  rw [Slop.runF_readReg]
  simp only []
  rw [Slop.runF_readReg]

end Slop.Equiv
