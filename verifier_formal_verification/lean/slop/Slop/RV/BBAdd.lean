import Slop.RV.BBMont
import Slop.RV.Tactic
import Slop.RV.Code.bb_add

/-! `bb_add` (plain Rust, `add_mod`). -/

namespace RV
open Spec
set_option maxHeartbeats 0

/-- `bb_add`: `a0, a1 < p` ⇒ `a0 ← (a0 + a1) mod p`. -/
def bbAddPost : State → State → Prop := fun s s' =>
  (s.getReg 10#5).toNat < BabyBearP → (s.getReg 11#5).toNat < BabyBearP →
    (s'.getReg 10#5).toNat = ((s.getReg 10#5).toNat + (s.getReg 11#5).toNat) % BabyBearP

theorem bb_add_impl : Implements Code.bb_add 16 bbAddPost := by
  intro s hcall
  rv_start Code.bb_add hcall
  rv_steps 16
  rv_ret
  refine ⟨by rv_regs, ?_, by rv_callee, by rv_frame⟩
  intro ha hb
  rv_regs
  rw [mask_sel]
  simp only [BabyBearP] at *
  split <;> rename_i h <;> simp only [BitVec.ult, decide_eq_true_eq] at h <;> bv_omega
end RV
