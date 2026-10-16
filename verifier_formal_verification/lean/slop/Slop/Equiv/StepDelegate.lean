import Slop.Equiv.Agree
import Slop.RV.Input

/-! Our step = an Airbender step for a delegation call: both run `RV.Delegation.blake2s` on the same registers and
memory, and write the same words. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

variable {s t : RV.State} {σ : SailState}

theorem storeWords_getReg (s : RV.State) (a : RV.Word) (ws : List RV.Word) (i : RV.Reg) :
    (s.storeWords a ws).getReg i = s.getReg i := by
  induction ws generalizing s a with
  | nil => rfl
  | cons w ws ih => exact (ih _ _).trans rfl

theorem storeWords_pc (s : RV.State) (a : RV.Word) (ws : List RV.Word) : (s.storeWords a ws).pc = s.pc := by
  induction ws generalizing s a with
  | nil => rfl
  | cons w ws ih => exact (ih _ _).trans rfl

/-- Sail's `writeWords` is our `storeWords`. -/
theorem writeWords_eq : ∀ (ws : List RV.Word) (σm : Nat → BitVec 8) (s : RV.State) (a : RV.Word),
    (∀ b : RV.Word, σm b.toNat = s.mem b) → a.toNat + 4 * ws.length < 2 ^ 32 →
    ∀ b : RV.Word, Airbender.writeWords σm a ws b.toNat = (s.storeWords a ws).mem b
  | [], _, _, _, hm, _, b => hm b
  | w :: ws, σm, s, a, hm, ha, b => by
    simp only [List.length_cons] at ha
    have hm' : ∀ c : RV.Word, writeBytes σm a.toNat 4 w c.toNat = (s.store a w 4).mem c := fun c => by
      have := write_eq4 σm s.mem hm a w (by omega) c
      rwa [BitVec.setWidth_eq] at this
    have ha' : (a + 4).toNat + 4 * ws.length < 2 ^ 32 := by
      rw [show (4 : RV.Word) = BitVec.ofNat 32 4 from rfl, word_add_toNat a 4 (by omega)]; omega
    exact writeWords_eq ws _ (s.store a w 4) (a + 4) hm' ha' b

/-- Not a delegation call: the Airbender machine takes a Sail step. -/
theorem delegation_none (h : Airbender.AgreeSail s σ) {i : RV.Instr}
    (hdec : RV.decode (RV.read s.mem s.pc 4) = some i) (hi : ∀ op, i ≠ .delegate op) :
    Airbender.delegation σ = none := by
  have hm : (fun a : RV.Word => σ.mem a.toNat) = s.mem := funext h.2.2.2
  unfold Airbender.delegation
  simp only [h.2.1, hm, hdec]
  by_cases hc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ Airbender.RAM_START
  · rw [if_pos hc]; cases i <;> first | rfl | exact absurd rfl (hi _)
  · rw [if_neg hc]

theorem kind_delegate (h : Airbender.AgreeSail s σ) (op : RV.CsrOp)
    (hc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ RV.ROM_END)
    (hdec : RV.decode (RV.read s.mem s.pc 4) = some (.delegate op)) (hex : RV.exec s (.delegate op) = some t) :
    ∃ σ', Airbender.delegation σ = some (some σ') ∧ Airbender.AgreeSail t σ' := by
  have hm : (fun a : RV.Word => σ.mem a.toNat) = s.mem := funext h.2.2.2
  have hr : ∀ i, Airbender.getReg σ i = s.getReg i := h.2.2.1
  simp only [RV.exec] at hex
  rcases hb : RV.Delegation.blake2s (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem with _ | ⟨n, x12, out⟩ <;>
    rw [hb] at hex
  · cases hex
  dsimp only at hex
  by_cases hrun : RV.isRun s.mem s.pc (RV.read s.mem s.pc 4) n
  case neg => rw [if_neg hrun] at hex; cases hex
  rw [if_pos hrun, Option.some.injEq] at hex
  subst hex
  have hbd := RV.blake2s_bound hb
  set pc' := s.pc + BitVec.ofNat 32 (4 * n)
  set σ₁ : SailState := { σ with mem := Airbender.writeWords σ.mem (s.getReg 10) out.toList }
  refine ⟨((xset σ₁ 12 x12).set .PC pc').set .nextPC pc', ?_, ?_, ?_, ?_, ?_⟩
  · unfold Airbender.delegation
    simp only [h.2.1, hm, hr, hdec, hb, if_pos hrun, if_pos (show s.pc.toNat % 4 = 0 ∧
      s.pc.toNat + 4 ≤ Airbender.RAM_START from hc), wX_run]
    rfl
  · exact sys_set (sys_set (sys_xset h.1 12 x12) .PC _ rfl) .nextPC _ rfl
  · rw [set_regs_ne _ _ _ _ (by decide), set_regs_self]; rfl
  · intro i
    rw [reg_eq, xget_set_nextPC, xget_set_PC, xget_xset]
    simp only [RV.State.getReg, RV.State.setReg, RV.State.setPC]
    have e : xget σ₁ i = xget σ i := rfl
    rw [e, ← reg_eq, hr]
    have := storeWords_getReg s (s.getReg 10) out.toList i
    simp only [RV.State.getReg] at this
    split_ifs <;> simp_all [RV.State.getReg]
  · intro a
    rw [show (((xset σ₁ 12 x12).set .PC pc').set .nextPC pc').mem = σ₁.mem by
      simp only [SailState.set, xset_mem]]
    exact writeWords_eq out.toList σ.mem s (s.getReg 10) h.2.2.2
      (by simp only [Vector.length_toList]; simp only [RV.RAM_END] at hbd; omega) a

end Slop.Equiv
