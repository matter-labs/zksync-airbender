import Slop.ISA.Equiv.Agree
import Slop.ISA.RV.Input

/-! Our step = an Airbender step for a delegation call: both apply `RV.Delegation.effect` of the same registers and
memory, so write the same words and the same register. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

variable {s t : RV.State} {σ : SailState}

theorem storeAll_getReg (s : RV.State) (ws : List (RV.Word × RV.Word)) (i : RV.Reg) :
    (s.storeAll ws).getReg i = s.getReg i := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih _).trans rfl

theorem storeAll_pc (s : RV.State) (ws : List (RV.Word × RV.Word)) : (s.storeAll ws).pc = s.pc := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih _).trans rfl

/-- Sail's `writeAll` is our `storeAll`. -/
theorem writeAll_eq : ∀ (ws : List (RV.Word × RV.Word)) (σm : Nat → BitVec 8) (s : RV.State),
    (∀ b : RV.Word, σm b.toNat = s.mem b) → (∀ aw ∈ ws, aw.1.toNat + 4 ≤ 2 ^ 32) →
    ∀ b : RV.Word, Airbender.writeAll σm ws b.toNat = (s.storeAll ws).mem b
  | [], _, _, hm, _, b => hm b
  | (a, w) :: ws, σm, s, hm, ha, b => by
    have hm' : ∀ c : RV.Word, writeBytes σm a.toNat 4 w c.toNat = (s.store a w 4).mem c := fun c => by
      have := write_eq4 σm s.mem hm a w (ha _ (List.mem_cons_self ..)) c
      rwa [BitVec.setWidth_eq] at this
    exact writeAll_eq ws _ (s.store a w 4) hm' (fun aw h => ha aw (List.mem_cons_of_mem _ h)) b

/-- Not a delegation call: the Airbender machine takes a Sail step. -/
theorem delegation_none (h : Airbender.AgreeSail s σ) {i : RV.Instr}
    (hdec : RV.decode (RV.read s.mem s.pc 4) = some i) (hi : ∀ k, i ≠ .delegate k) :
    Airbender.delegation σ = none := by
  have hm : (fun a : RV.Word => σ.mem a.toNat) = s.mem := funext h.2.2.2
  unfold Airbender.delegation
  simp only [h.2.1, hm, hdec]
  by_cases hc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ Airbender.RAM_START
  · rw [if_pos hc]; cases i <;> first | rfl | exact absurd rfl (hi _)
  · rw [if_neg hc]

/-- Applying the same effect to agreeing states gives agreeing states. -/
theorem applyEffect_agree (h : Airbender.AgreeSail s σ) (e : RV.Effect) (hex : s.applyEffect e = some t) :
    ∃ σ', Airbender.applyEffect σ e = some σ' ∧ Airbender.AgreeSail t σ' := by
  have hr : ∀ i, Airbender.getReg σ i = s.getReg i := h.2.2.1
  unfold RV.State.applyEffect at hex
  split_ifs at hex with hw
  rw [Option.some.injEq] at hex
  subst hex
  have hbd : ∀ aw ∈ e.writes, aw.1.toNat + 4 ≤ 2 ^ 32 := fun aw haw => by
    have := of_decide_eq_true (List.all_eq_true.1 hw aw haw)
    simp only [RV.writable, RV.RAM_END] at this; omega
  set pc' := σ.regs .PC + 4
  set σ₁ : SailState := { σ with mem := Airbender.writeAll σ.mem e.writes }
  refine ⟨((xset σ₁ e.reg e.val).set .PC pc').set .nextPC pc', ?_, ?_, ?_, ?_, ?_⟩
  · unfold Airbender.applyEffect
    simp only [if_pos hw, wX_run]
    rfl
  · exact sys_set (sys_set (sys_xset (show Airbender.Configured σ₁ from h.1) _ _) .PC _ rfl) .nextPC _ rfl
  · rw [set_regs_ne _ _ _ _ (by decide), set_regs_self]
    simp only [pc', RV.State.nextInstr, RV.State.setReg, storeAll_pc, h.2.1]
  · intro i
    rw [reg_eq, xget_set_nextPC, xget_set_PC, xget_xset]
    have e₁ : xget σ₁ i = xget σ i := rfl
    rw [e₁, ← reg_eq, hr]
    have := storeAll_getReg s e.writes i
    simp only [RV.State.getReg, RV.State.setReg, RV.State.nextInstr] at this ⊢
    split <;> simp_all
  · intro a
    rw [show (((xset σ₁ e.reg e.val).set .PC pc').set .nextPC pc').mem = σ₁.mem by
      simp only [SailState.set, xset_mem]]
    have := writeAll_eq e.writes σ.mem s h.2.2.2 hbd a
    simp only [RV.State.nextInstr, RV.State.setReg] at this ⊢
    exact this

theorem kind_delegate (h : Airbender.AgreeSail s σ) (k : RV.DelegationKind)
    (hc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ RV.ROM_END)
    (hdec : RV.decode (RV.read s.mem s.pc 4) = some (.delegate k)) (hex : RV.exec s (.delegate k) = some t) :
    ∃ σ', Airbender.delegation σ = some (some σ') ∧ Airbender.AgreeSail t σ' := by
  have hm : (fun a : RV.Word => σ.mem a.toNat) = s.mem := funext h.2.2.2
  have hr : ∀ i, Airbender.getReg σ i = s.getReg i := h.2.2.1
  simp only [RV.exec] at hex
  rcases he : RV.Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem with _ | e <;>
    rw [he] at hex
  · cases hex
  obtain ⟨σ', h₁, h₂⟩ := applyEffect_agree h e hex
  refine ⟨σ', ?_, h₂⟩
  unfold Airbender.delegation
  simp only [h.2.1, hm, hr, hdec, he, ite_cond_eq_true _ _ (eq_true (show s.pc.toNat % 4 = 0 ∧
    s.pc.toNat + 4 ≤ Airbender.RAM_START from hc)), Option.bind_some, h₁]

end Slop.Equiv
