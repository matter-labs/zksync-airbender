import Slop.Equiv.Agree
import Slop.Equiv.ExecLoad
import Slop.RV.Input
import Slop.RV.DecodeShape

/-! Our step = an Airbender step for the input read `csrrw rd, 0x7c0, x0` (an Airbender deviation from Sail, which
has no CSR 0x7c0): both sides write the next input word to `rd`. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

variable {s t : RV.State} {σ : SailState} {next : BitVec 32}

/-- Our CSR 0x7c0 rows: a read has `rd ≠ x0`, a write a nonzero source. -/
theorem decode_csr {w : BitVec 32} {i : RV.Instr} (h : RV.decode w = some i) :
    (∀ rd, i = .inputRead rd → rd ≠ 0) ∧ (∀ src, i = .inputWrite src → src ≠ 0) := by
  have hs := RV.decode_shape h
  exact ⟨fun rd e => by subst e; exact hs, fun src e => by subst e; exact hs⟩

theorem exec_input (σ : SailState) (rd : BitVec 5) (hrd : rd ≠ 0) :
    runSail (Airbender.execute next (Airbender.toSail (.inputRead rd))) σ = .ok RETIRE_SUCCESS (xset σ rd next) := by
  simp only [Airbender.toSail, Airbender.csrToSail, Airbender.execute, Airbender.nonDeterminism,
    show ((0x7c0 : BitVec 12) == 0x7c0) = true from rfl, show (regidx.Regidx 0 == zreg) = true from rfl,
    ite_true, bne, regidx_beq_zreg rd hrd, Bool.not_false, Bool.and_true, Bool.true_and, Slop.runF_bind, wX_run,
    Slop.runF_pure]

theorem exec_write (σ : SailState) (src : BitVec 5) (hsrc : src ≠ 0) :
    runSail (Airbender.execute next (Airbender.toSail (.inputWrite src))) σ = .ok RETIRE_SUCCESS σ := by
  simp only [Airbender.toSail, Airbender.csrToSail, Airbender.execute, Airbender.nonDeterminism,
    show ((0x7c0 : BitVec 12) == 0x7c0) = true from rfl, show (regidx.Regidx 0 == zreg) = true from rfl,
    regidx_beq_zreg src hsrc, ite_true, ite_false, bne, Bool.not_false, Bool.not_true, Bool.and_true,
    Bool.true_and, Bool.false_and, Bool.and_false, Bool.false_eq_true, Slop.runF_pure] <;> rfl

theorem kind_input (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (rd : BitVec 5)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.inputRead rd)) :
    ∃ σ', stepSail next σ = some (σ', true) ∧ Airbender.AgreeSail (s.setReg rd next).nextInstr σ' :=
  step_write h ha h2 _ hdec rd next (exec_input _ rd ((decode_csr hdec).1 rd rfl))

theorem kind_write (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (src : BitVec 5)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.inputWrite src))
    (ht : RV.exec s (.inputWrite src) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  exact step_next h ha h2 _ hdec (exec_write _ src ((decode_csr hdec).2 src rfl))

end Slop.Equiv
