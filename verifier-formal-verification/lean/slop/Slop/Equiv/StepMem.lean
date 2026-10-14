import Slop.Equiv.StepJump
import Slop.Equiv.ExecLoad

/-! Our step = an Airbender step, for loads and stores. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

variable {s t : RV.State} {σ : FState}

/-- The loaded value, Sail's way = ours. -/
theorem load_val (σm : Nat → BitVec 8) (sm : BitVec 32 → BitVec 8) (hm : ∀ b : BitVec 32, σm b.toNat = sm b)
    (a : BitVec 32) (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4) (h : a.toNat + n ≤ 2 ^ 32) (sg : Bool) :
    extend_value (!sg) (readBytes σm a.toNat n) =
      if sg then ((RV.read sm a n).setWidth (8 * n)).signExtend 32 else RV.read sm a n := by
  rcases hn with rfl | rfl | rfl
  all_goals
    first | rw [read_eq1 σm sm hm a h] | rw [read_eq2 σm sm hm a h] | rw [read_eq4 σm sm hm a h]
    cases sg <;> simp [extend_value, zero_extend, sign_extend, Sail.BitVec.zeroExtend, Sail.BitVec.signExtend]

theorem ram_end_lt : RV.RAM_END < 2 ^ 32 := by decide

theorem kind_load (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (n : Nat) (sg : Bool) (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (rd rs1 : BitVec 5) (x : BitVec 12)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.load n sg rd rs1 (x.signExtend 32)))
    (ht : RV.exec s (.load n sg rd rs1 (x.signExtend 32)) = some t) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree t σ' := by
  simp only [RV.exec] at ht
  by_cases hz : rd = 0
  · subst hz
    rw [if_pos rfl, Option.some.injEq] at ht; subst ht
    exact step_next h ha h2 _ hdec (exec_load_x0 _ rs1 _ n sg)
  · rw [if_neg hz] at ht
    by_cases hc : RV.aligned (s.r rs1 + x.signExtend 32) n ∧ RV.readable (s.r rs1 + x.signExtend 32) n
    case neg => rw [if_neg hc] at ht; cases ht
    rw [if_pos hc, Option.some.injEq] at ht; subst ht
    obtain ⟨hal, hrd⟩ := hc
    have hx : xget (σ.set .nextPC (σ.regs .PC + 4)) rs1 = s.r rs1 := by rw [xget_set_nextPC, agree_xget h]
    have e := exec_load (σ.set .nextPC (σ.regs .PC + 4)) (sys_set h.1 .nextPC _ rfl) rd rs1 x n sg hn hz
      (by rw [hx]; exact hal) (by rw [hx]; exact hrd)
    rw [hx] at e
    have hv : extend_value (!sg) (readBytes (σ.set .nextPC (σ.regs .PC + 4)).mem (s.r rs1 + x.signExtend 32).toNat n)
        = _ := load_val σ.mem s.mem h.2.2.2 _ n hn (by have := ram_end_lt; simp only [RV.readable] at hrd; omega) sg
    rw [hv] at e
    exact step_write h ha h2 _ hdec rd _ e

theorem kind_store (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (rs2 rs1 : BitVec 5) (x : BitVec 12)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.store n rs2 rs1 (x.signExtend 32)))
    (ht : RV.exec s (.store n rs2 rs1 (x.signExtend 32)) = some t) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree t σ' := by
  simp only [RV.exec] at ht
  by_cases hc : RV.aligned (s.r rs1 + x.signExtend 32) n ∧ RV.writable (s.r rs1 + x.signExtend 32) n
  case neg => rw [if_neg hc] at ht; cases ht
  rw [if_pos hc, Option.some.injEq] at ht; subst ht
  obtain ⟨hal, hw1, hw2⟩ := hc
  have hx : xget (σ.set .nextPC (σ.regs .PC + 4)) rs1 = s.r rs1 := by rw [xget_set_nextPC, agree_xget h]
  have hx2 : xget (σ.set .nextPC (σ.regs .PC + 4)) rs2 = s.r rs2 := by rw [xget_set_nextPC, agree_xget h]
  have e := exec_store (σ.set .nextPC (σ.regs .PC + 4)) (sys_set h.1 .nextPC _ rfl) rs2 rs1 x n hn
    (by rw [hx]; exact hal) (by rw [hx]; exact hw1) (by rw [hx]; exact hw2)
  rw [hx, hx2] at e
  have hpcs : σ.regs .PC = s.pc := h.2.1
  refine step_agree h ha h2 _ hdec _ e (sys_of_regs (sys_set h.1 .nextPC _ rfl) rfl) ?_ ?_ ?_ ?_
  · show (σ.set .nextPC (σ.regs .PC + 4)).regs .nextPC = s.pc + 4
    rw [set_regs_self, hpcs]
  · show (s.pc + 4).toNat % 4 = 0
    rw [← hpcs]; exact pc4_aligned _ ha h2
  · intro j
    change xget (σ.set .nextPC (σ.regs .PC + 4)) j = s.r j
    rw [xget_set_nextPC, agree_xget h]
  · intro a
    show writeBytes σ.mem _ n _ a.toNat = RV.write s.mem _ (s.r rs2) n a
    have := ram_end_lt
    simp only [RV.RAM_END] at hw2 this
    rcases hn with rfl | rfl | rfl
    · exact write_eq1 σ.mem s.mem h.2.2.2 _ _ (by omega) a
    · exact write_eq2 σ.mem s.mem h.2.2.2 _ _ (by omega) a
    · exact write_eq4 σ.mem s.mem h.2.2.2 _ _ (by omega) a

end Slop.Equiv
