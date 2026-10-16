import Slop.Equiv.StepIsAirbender
import Slop.Equiv.StepDelegate
import Slop.RV.Stuck

/-! The Airbender machine is stuck where our spec is stuck at `zksync_os_finish_error` (`csrrw x0, cycle, x0`: no
row of the decoding table), and runs of the machine compose. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem airbender_stuck {T : RV.State} {m : Airbender.Machine} (h : Airbender.Agree T m) (hT : RV.AtFinishError T) :
    Airbender.step m = none := by
  obtain ⟨ha, hrom, hw⟩ := hT
  have hA := h.1
  have hpc : m.sail.regs .PC = T.pc := hA.2.1
  have hm : (fun a : RV.Word => m.sail.mem a.toNat) = T.mem := funext hA.2.2.2
  have hrd : readBytes m.sail.mem (m.sail.regs .PC).toNat 4 = 0xc0001073#32 := by
    rw [← BitVec.setWidth_eq (readBytes _ _ 4), hpc, ← read_eq4 m.sail.mem T.mem hA.2.2.2 _
      (by simp only [RV.ROM_END] at hrom; omega), hw]
  have hdel : Airbender.delegation m.sail = none := by
    unfold Airbender.delegation
    simp only [hpc, hm, hw, show RV.decode 0xc0001073#32 = none by decide +kernel]
    split_ifs <;> rfl
  have hf := fetch_rom m.sail hA.1 (by rw [hpc]; exact ha) (by rw [hpc]; simp only [Airbender.RAM_START]; exact hrom)
    (by rw [hrd]; decide)
  unfold Airbender.step
  rw [hdel]
  dsimp only
  have : runSail (Airbender.sailStep (m.input.headD 0)) m.sail = .ok none m.sail := by
    unfold Airbender.sailStep
    simp only [Slop.runF_bind, hf, hrd, show RV.decode 0xc0001073#32 = none by decide +kernel, Slop.runF_pure]
  rw [this]

theorem arun_add : ∀ (n k : Nat) (m : Airbender.Machine),
    Airbender.run (n + k) m = (Airbender.run n m).bind (Airbender.run k)
  | 0, k, m => by simp [Airbender.run]
  | n + 1, k, m => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Airbender.run]
    cases Airbender.step m <;> simp [arun_add n k]

end Slop.Equiv
