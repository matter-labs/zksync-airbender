import Slop.ISA.Equiv.Agree
import Slop.ISA.RV.Input

/-! Our step = an Airbender step for a delegation call: both apply `RV.Delegation.effect` of the same registers and
RAM (ours `mem`; the machine's shadow RAM below `ROM_END`, Sail's memory above), so write the same words and the
same register. -/

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

/-- `storeAll`'s RAM depends only on the RAM it starts from. -/
theorem storeAll_mem_congr (s s' : RV.State) (ws : List (RV.Word × RV.Word)) (h : s.mem = s'.mem) :
    (s.storeAll ws).mem = (s'.storeAll ws).mem := by
  induction ws generalizing s s' with
  | nil => exact h
  | cons w ws ih =>
    obtain ⟨a, v⟩ := w
    exact ih (s.store a v 4) (s'.store a v 4) (by simp only [RV.State.store, h])

/-- Under the agreement, the machine's RAM view (shadow RAM below `ROM_END`, Sail's memory above) is our RAM. -/
theorem ramView_eq (h : Airbender.AgreeSail s σ) {shadow : Airbender.Shadow}
    (hsh : ∀ a : RV.Word, a.toNat < RV.ROM_END → shadow a = s.mem a) : Airbender.ramView σ shadow = s.mem := by
  funext a
  unfold Airbender.ramView
  split
  · exact hsh a ‹_›
  · rw [h.2.2.2 a, RV.loadView_high _ _ (by omega)]

/-- The machine's fetch (from Sail's memory) reads the ROM image. -/
theorem fetch_rom_read (h : Airbender.AgreeSail s σ) (hc : s.pc.toNat + 4 ≤ RV.ROM_END) :
    RV.read (fun a : RV.Word => σ.mem a.toNat) s.pc 4 = RV.read s.rom s.pc 4 := by
  rw [show (fun a : RV.Word => σ.mem a.toNat) = s.loadView from funext h.2.2.2]
  exact RV.read_loadView_rom s s.pc 4 hc

/-- Not a delegation call: the Airbender machine takes a Sail step. -/
theorem delegation_none (h : Airbender.AgreeSail s σ) (shadow : Airbender.Shadow) {i : RV.Instr}
    (hdec : RV.decode (RV.read s.rom s.pc 4) = some i) (hi : ∀ k, i ≠ .delegate k) :
    Airbender.delegation σ shadow = none := by
  unfold Airbender.delegation
  simp only [h.2.1]
  by_cases hc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ Airbender.RAM_START
  · rw [if_pos hc, fetch_rom_read h hc.2, hdec]; cases i <;> first | rfl | exact absurd rfl (hi _)
  · rw [if_neg hc]

/-- Applying the same effect to agreeing states gives agreeing states. -/
theorem applyEffect_agree (h : Airbender.AgreeSail s σ) {shadow : Airbender.Shadow}
    (hsh : ∀ a : RV.Word, a.toNat < RV.ROM_END → shadow a = s.mem a) (e : RV.Effect)
    (hex : s.applyEffect e = some t) :
    ∃ σ' shadow', Airbender.applyEffect σ shadow e = some (σ', shadow') ∧ Airbender.AgreeSail t σ' ∧
      ∀ a : RV.Word, a.toNat < RV.ROM_END → shadow' a = t.mem a := by
  have hr : ∀ i, Airbender.getReg σ i = s.getReg i := h.2.2.1
  unfold RV.State.applyEffect at hex
  split_ifs at hex with hw
  rw [Option.some.injEq] at hex
  subst hex
  have hram : (({ pc := 0, regFile := fun _ => 0, rom := fun _ => 0, mem := Airbender.ramView σ shadow } :
      RV.State).storeAll e.writes).mem = (s.storeAll e.writes).mem :=
    storeAll_mem_congr _ _ _ (ramView_eq h hsh)
  obtain ⟨ram, hramdef⟩ : ∃ ram, ram = (s.storeAll e.writes).mem := ⟨_, rfl⟩
  have tmem : (((s.storeAll e.writes).setReg e.reg e.val).nextInstr).mem = ram := by
    rw [hramdef]; rfl
  have trom : (((s.storeAll e.writes).setReg e.reg e.val).nextInstr).rom = s.rom := RV.storeAll_rom s e.writes
  let pc' := σ.regs .PC + 4
  let σ₁ : SailState :=
    { σ with mem := fun n => if RV.ROM_END ≤ n ∧ n < 2 ^ 32 then ram (BitVec.ofNat 32 n) else σ.mem n }
  refine ⟨((xset σ₁ e.reg e.val).set .PC pc').set .nextPC pc',
    fun a => if a.toNat < RV.ROM_END then ram a else shadow a, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · unfold Airbender.applyEffect
    simp only [if_pos hw, wX_run, hram, ← hramdef]
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
    show (if RV.ROM_END ≤ a.toNat ∧ a.toNat < 2 ^ 32 then ram (BitVec.ofNat 32 a.toNat) else σ.mem a.toNat) = _
    by_cases ha : a.toNat < RV.ROM_END
    · rw [if_neg (by omega), h.2.2.2 a, RV.loadView_low _ _ ha, RV.loadView_low _ _ ha, trom]
    · rw [if_pos ⟨by omega, a.isLt⟩, RV.loadView_high _ _ (by omega), tmem, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
  · intro a ha
    simp only [if_pos ha, tmem]

theorem kind_delegate (h : Airbender.AgreeSail s σ) {shadow : Airbender.Shadow}
    (hsh : ∀ a : RV.Word, a.toNat < RV.ROM_END → shadow a = s.mem a) (k : RV.DelegationKind)
    (hc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ RV.ROM_END)
    (hdec : RV.decode (RV.read s.rom s.pc 4) = some (.delegate k)) (hex : RV.exec s (.delegate k) = some t) :
    ∃ σ' shadow', Airbender.delegation σ shadow = some (some (σ', shadow')) ∧ Airbender.AgreeSail t σ' ∧
      ∀ a : RV.Word, a.toNat < RV.ROM_END → shadow' a = t.mem a := by
  have hr : ∀ i, Airbender.getReg σ i = s.getReg i := h.2.2.1
  simp only [RV.exec, RV.State.delegationRAM] at hex
  rcases he : RV.Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem with _ | e <;>
    rw [he] at hex
  · cases hex
  obtain ⟨σ', shadow', h₁, h₂, h₃⟩ := applyEffect_agree h hsh e hex
  refine ⟨σ', shadow', ?_, h₂, h₃⟩
  unfold Airbender.delegation
  simp only [h.2.1, hr, ite_cond_eq_true _ _ (eq_true (show s.pc.toNat % 4 = 0 ∧
    s.pc.toNat + 4 ≤ Airbender.RAM_START from hc)), fetch_rom_read h hc.2, hdec, ramView_eq h hsh, he,
    Option.bind_some, h₁]

end Slop.Equiv
