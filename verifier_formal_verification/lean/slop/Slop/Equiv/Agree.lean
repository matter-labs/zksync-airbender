import Slop.Equiv.Bridge

/-! Bookkeeping for `Airbender.Agree` across one step: what `set`/`xset` leave unchanged, and the core lemma
`step_agree` (one Airbender step whose result matches our step on PC, registers and memory). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem set_regs_self (σ : SailState) (r : Register) (v : RegisterType r) : (σ.set r v).regs r = v := by
  simp [SailState.set]

theorem set_regs_ne (σ : SailState) (r r' : Register) (v : RegisterType r) (h : r ≠ r') :
    (σ.set r v).regs r' = σ.regs r' := by
  simp [SailState.set, h]

theorem set_set (σ : SailState) (r : Register) (v w : RegisterType r) : (σ.set r v).set r w = σ.set r w := by
  cases σ; simp only [SailState.set, SailState.mk.injEq, and_true]; funext r'; split <;> simp_all

theorem xget_set_nextPC (σ : SailState) (v : BitVec 32) (i : BitVec 5) : xget (σ.set .nextPC v) i = xget σ i := by
  obtain ⟨⟨n, hn⟩⟩ := i
  interval_cases n <;> rfl

theorem xget_set_PC (σ : SailState) (v : BitVec 32) (i : BitVec 5) : xget (σ.set .PC v) i = xget σ i := by
  obtain ⟨⟨n, hn⟩⟩ := i
  interval_cases n <;> rfl

theorem xset_nextPC (σ : SailState) (i : BitVec 5) (v : BitVec 32) : (xset σ i v).regs .nextPC = σ.regs .nextPC :=
  xset_regs σ i v .nextPC (by simp)

theorem xset_PC (σ : SailState) (i : BitVec 5) (v : BitVec 32) : (xset σ i v).regs .PC = σ.regs .PC :=
  xset_regs σ i v .PC (by simp)

theorem agree_xget {s : RV.State} {σ : SailState} (h : Airbender.Agree s σ) (i : BitVec 5) : xget σ i = s.getReg i := by
  rw [← reg_eq]; exact h.2.2.1 i

/-- One Airbender step, given what `execute` does, agrees with our step if the results agree. -/
theorem step_agree {s t : RV.State} {σ : SailState} (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (i : RV.Instr)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some i) (σ2 : SailState)
    (hexec : runSail (Airbender.execute (Airbender.toSail i)) (σ.set .nextPC (σ.regs .PC + 4)) = .ok RETIRE_SUCCESS σ2)
    (hs2 : Airbender.Configured σ2) (hpc : σ2.regs .nextPC = t.pc) (hal : t.pc.toNat % 4 = 0)
    (hr : ∀ j, xget σ2 j = t.getReg j) (hm : ∀ a : RV.Word, σ2.mem a.toNat = t.mem a) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree t σ' := by
  refine ⟨_, step_of_exec σ h.1 ha h2 i hdec σ2 hexec (hpc ▸ hal), ?_, ?_, ?_, ?_⟩
  · exact sys_set hs2 .PC _ rfl
  · rw [set_regs_self, hpc]
  · intro j; rw [reg_eq, xget_set_PC, hr]
  · intro a; exact hm a

/-- `PC + 4` stays aligned (no wrap: the PC is in ROM). -/
theorem pc4_aligned (pc : BitVec 32) (ha : pc.toNat % 4 = 0) (h2 : pc.toNat + 4 ≤ Airbender.RAM_START) :
    (pc + 4).toNat % 4 = 0 := by
  have := word_add_toNat pc 4 (by simp only [Airbender.RAM_START, RV.ROM_END] at h2; omega)
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, this]; omega

/-- The usual outcome: write `v` to `rd`, go to the next instruction. -/
theorem step_write {s : RV.State} {σ : SailState} (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (i : RV.Instr)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some i) (rd : BitVec 5) (v : BitVec 32)
    (hexec : runSail (Airbender.execute (Airbender.toSail i)) (σ.set .nextPC (σ.regs .PC + 4)) =
      .ok RETIRE_SUCCESS (xset (σ.set .nextPC (σ.regs .PC + 4)) rd v)) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree (s.setReg rd v).nextInstr σ' := by
  have hpcs : σ.regs .PC = s.pc := h.2.1
  refine step_agree h ha h2 i hdec _ hexec (sys_xset (sys_set h.1 .nextPC _ rfl) rd v) ?_ ?_ ?_ ?_
  · rw [xset_nextPC, set_regs_self, hpcs]; rfl
  · show (s.pc + 4).toNat % 4 = 0
    rw [← hpcs]; exact pc4_aligned _ ha h2
  · intro j
    rw [xget_xset, xget_set_nextPC, agree_xget h]
    simp only [RV.State.getReg, RV.State.setReg, RV.State.nextInstr]
    split_ifs <;> simp_all
  · intro a; rw [xset_mem]; exact h.2.2.2 a

/-- Nothing but the next instruction. -/
theorem step_next {s : RV.State} {σ : SailState} (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (i : RV.Instr)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some i)
    (hexec : runSail (Airbender.execute (Airbender.toSail i)) (σ.set .nextPC (σ.regs .PC + 4)) =
      .ok RETIRE_SUCCESS (σ.set .nextPC (σ.regs .PC + 4))) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree s.nextInstr σ' := by
  have hpcs : σ.regs .PC = s.pc := h.2.1
  refine step_agree h ha h2 i hdec _ hexec (sys_set h.1 .nextPC _ rfl) ?_ ?_ ?_ ?_
  · rw [set_regs_self, hpcs]; rfl
  · show (s.pc + 4).toNat % 4 = 0
    rw [← hpcs]; exact pc4_aligned _ ha h2
  · intro j; rw [xget_set_nextPC, agree_xget h]; rfl
  · intro a; exact h.2.2.2 a

/-- A jump to `T` (aligned) that links `L` into `rd`. -/
theorem step_jump {s : RV.State} {σ : SailState} (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (i : RV.Instr)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some i) (rd : BitVec 5) (T L : BitVec 32)
    (hT : T.toNat % 4 = 0)
    (hexec : runSail (Airbender.execute (Airbender.toSail i)) (σ.set .nextPC (σ.regs .PC + 4)) =
      .ok RETIRE_SUCCESS (xset ((σ.set .nextPC (σ.regs .PC + 4)).set .nextPC T) rd L)) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree ((s.setPC T).setReg rd L) σ' := by
  refine step_agree h ha h2 i hdec _ hexec
    (sys_xset (sys_set (sys_set h.1 .nextPC _ rfl) .nextPC _ rfl) rd L) ?_ hT ?_ ?_
  · rw [xset_nextPC, set_regs_self]; rfl
  · intro j
    rw [xget_xset, xget_set_nextPC, xget_set_nextPC, agree_xget h]
    simp only [RV.State.getReg, RV.State.setReg, RV.State.setPC]
    split_ifs <;> simp_all
  · intro a; rw [xset_mem]; exact h.2.2.2 a

/-- A taken branch to `T` (aligned). -/
theorem step_goto {s : RV.State} {σ : SailState} (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (i : RV.Instr)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some i) (T : BitVec 32) (hT : T.toNat % 4 = 0)
    (hexec : runSail (Airbender.execute (Airbender.toSail i)) (σ.set .nextPC (σ.regs .PC + 4)) =
      .ok RETIRE_SUCCESS ((σ.set .nextPC (σ.regs .PC + 4)).set .nextPC T)) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree (s.setPC T) σ' := by
  refine step_agree h ha h2 i hdec _ hexec (sys_set (sys_set h.1 .nextPC _ rfl) .nextPC _ rfl) ?_ hT ?_ ?_
  · rw [set_regs_self]; rfl
  · intro j; rw [xget_set_nextPC, xget_set_nextPC, agree_xget h]; rfl
  · intro a; exact h.2.2.2 a

end Slop.Equiv
