import Human.ISA.RV32
import Slop.ISA.RV.Mem
import Slop.ISA.RV.Attr

/-! Rewriting lemmas for symbolic runs on the RV32 spec. -/

namespace RV

-- State accessors. Proved by `Eq.trans rfl rfl`, not `rfl`, on purpose: simp then rewrites with explicit proofs
-- instead of definitional steps, which otherwise made simp hang / the kernel recurse deeply on big symbolic states.
@[simp] theorem r_zero (s : State) : s.getReg 0 = 0 := Eq.trans rfl rfl
/-- `x0` in the literal form the step simp set uses. -/
theorem r_zero5 (s : State) : s.getReg 0#5 = 0#32 := Eq.trans rfl rfl
@[simp] theorem set_pc (s : State) rd v : (s.setReg rd v).pc = s.pc := Eq.trans rfl rfl
@[simp] theorem set_mem (s : State) rd v : (s.setReg rd v).mem = s.mem := Eq.trans rfl rfl
@[simp] theorem next_pc (s : State) : s.nextInstr.pc = s.pc + 4 := Eq.trans rfl rfl
@[simp] theorem next_mem (s : State) : s.nextInstr.mem = s.mem := Eq.trans rfl rfl
@[simp] theorem next_r (s : State) i : s.nextInstr.getReg i = s.getReg i := Eq.trans rfl rfl
@[simp] theorem store_r (s : State) a v n i : (s.store a v n).getReg i = s.getReg i := Eq.trans rfl rfl
@[simp] theorem store_pc (s : State) a v n : (s.store a v n).pc = s.pc := Eq.trans rfl rfl
@[simp] theorem store_mem (s : State) a v n : (s.store a v n).mem = write s.mem a v n := Eq.trans rfl rfl
@[simp] theorem jump_r (s : State) t i : (s.setPC t).getReg i = s.getReg i := Eq.trans rfl rfl
@[simp] theorem jump_pc (s : State) t : (s.setPC t).pc = t := Eq.trans rfl rfl
@[simp] theorem jump_mem (s : State) t : (s.setPC t).mem = s.mem := Eq.trans rfl rfl

@[simp] theorem r_set (s : State) (rd : Reg) (v : Word) (i : Reg) :
    (s.setReg rd v).getReg i = if i = 0 then 0 else if i = rd then v else s.getReg i := by
  simp only [State.getReg, State.setReg]
  split <;> simp_all

theorem r_set_x0 (s : State) (rd : Reg) (v : Word) (i : Reg) (h : i = 0) : (s.setReg rd v).getReg i = 0 := by
  subst h; rfl
theorem r_set_hit (s : State) (rd : Reg) (v : Word) (h : ¬ rd = 0) : (s.setReg rd v).getReg rd = v := by
  simp only [State.getReg, State.setReg, ite_true, h, ite_false]
theorem r_set_miss (s : State) (rd : Reg) (v : Word) (i : Reg) (h1 : ¬ i = 0) (h2 : ¬ i = rd) :
    (s.setReg rd v).getReg i = s.getReg i := by
  simp only [State.getReg, State.setReg, h1, h2, ite_false]

open Lean Meta Simp in
/-- `(s.setReg rd v).getReg i` for literal register numbers: `v`, `s.getReg i` or `0` directly (no `if`). -/
simproc reduceRSet (State.getReg (State.setReg _ _ _) _) := fun e => do
  let_expr State.getReg st i := e | return .continue
  let_expr State.setReg s rd v := st | return .continue
  let some ⟨_, iv⟩ ← getBitVecValue? i | return .continue
  let some ⟨_, rdv⟩ ← getBitVecValue? rd | return .continue
  let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Reg, mkRawNatLit 0, none]
  if iv.toNat = 0 then
    let zeroW ← mkAppOptM ``OfNat.ofNat #[mkConst ``Word, mkRawNatLit 0, none]
    let pf := mkApp5 (mkConst ``r_set_x0) s rd v i (← mkDecideProof (← mkEq i zero))
    return .done { expr := zeroW, proof? := some (← mkExpectedTypeHint pf (← mkEq e zeroW)) }
  let hi0 ← mkDecideProof (mkNot (← mkEq i zero))
  if iv.toNat = rdv.toNat then
    let hrd0 ← mkDecideProof (mkNot (← mkEq rd zero))
    let pf ← mkAppM ``r_set_hit #[s, rd, v, hrd0]
    let pf ← mkExpectedTypeHint pf (← mkEq e v)
    return .done { expr := v, proof? := some pf }
  let hne ← mkDecideProof (mkNot (← mkEq i rd))
  let r := mkApp2 (mkConst ``State.getReg) s i
  let pf := mkApp6 (mkConst ``r_set_miss) s rd v i hi0 hne
  return .done { expr := r, proof? := some (← mkExpectedTypeHint pf (← mkEq e r)) }

theorem goto_ok (s : State) (t : Word) (h : t.toNat % 4 = 0) : s.jumpAligned t = some (s.setPC t) := by
  simp [State.jumpAligned, h]

theorem run_succ (n : Nat) (s : State) : run (n + 1) s = (step s).bind (run n) := rfl

theorem step_fetch (s : State) (w : Word) (hpc : s.pc.toNat % 4 = 0) (hrom : s.pc.toNat + 4 ≤ ROM_END)
    (hw : read s.mem s.pc 4 = w) : step s = (decode w).bind (exec s) := by
  simp [step, hpc, hrom, hw]

theorem step_ok (s : State) (hpc : s.pc.toNat % 4 = 0) (hrom : s.pc.toNat + 4 ≤ ROM_END) :
    step s = (decode (read s.mem s.pc 4)).bind (exec s) := by
  simp [step, hpc, hrom]

/-! Goal-directed running: the goal is `∃ m s', run m S = some s' ∧ P s'`. -/

theorem run_add (n m : Nat) (s : State) : run (n + m) s = (run n s).bind (run m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.add_right_comm, run_succ, run_succ]
    cases step s with
    | none => rfl
    | some t => exact ih t

theorem run_of_step (S : State) (P : State → Prop)
    (h : (step S).elim False (fun T => ∃ m s', run m T = some s' ∧ P s')) : ∃ m s', run m S = some s' ∧ P s' := by
  cases hs : step S with
  | none => simp [hs] at h
  | some T =>
    simp only [hs, Option.elim] at h
    obtain ⟨m, s', h1, h2⟩ := h
    exact ⟨m + 1, s', by simp [run_succ, hs, h1], h2⟩

theorem run_of_run (S S1 : State) (n : Nat) (P : State → Prop) (h1 : run n S = some S1)
    (h : ∃ m s', run m S1 = some s' ∧ P s') : ∃ m s', run m S = some s' ∧ P s' := by
  obtain ⟨m, s', h2, h3⟩ := h
  exact ⟨n + m, s', by simp [run_add, h1, h2], h3⟩

theorem exists_run_mono {U : State} {P Q : State → Prop} (H : ∃ m s', run m U = some s' ∧ Q s')
    (h : ∀ s', Q s' → P s') : ∃ m s', run m U = some s' ∧ P s' := by
  obtain ⟨m, s', h1, h2⟩ := H
  exact ⟨m, s', h1, h s' h2⟩

theorem run_done (S : State) (P : State → Prop) (h : P S) : ∃ m s', run m S = some s' ∧ P s' := ⟨0, S, rfl, h⟩

/-- Run to a state with `Q`, then on from there. -/
theorem run_cont {S : State} {P Q : State → Prop} (H : ∃ m S', run m S = some S' ∧ Q S')
    (h : ∀ S', Q S' → ∃ m s', run m S' = some s' ∧ P s') : ∃ m s', run m S = some s' ∧ P s' := by
  obtain ⟨m, S', h1, h2⟩ := H
  exact run_of_run S S' m P h1 (h S' h2)

/-! `exec`, one lemma per instruction kind; side conditions are left to the discharger. -/

theorem exec_lui (s : State) rd imm : exec s (.lui rd imm) = some (s.setReg rd imm).nextInstr := rfl
theorem exec_auipc (s : State) rd imm : exec s (.auipc rd imm) = some (s.setReg rd (s.pc + imm)).nextInstr := rfl
theorem exec_opImm (s : State) op rd rs1 imm :
    exec s (.opImm op rd rs1 imm) = some (s.setReg rd (alu op (s.getReg rs1) imm)).nextInstr := rfl
theorem exec_op (s : State) op rd rs1 rs2 :
    exec s (.op op rd rs1 rs2) = some (s.setReg rd (alu op (s.getReg rs1) (s.getReg rs2))).nextInstr := rfl
theorem exec_jal (s : State) rd off (h : (s.pc + off).toNat % 4 = 0) :
    exec s (.jal rd off) = some ((s.setPC (s.pc + off)).setReg rd (s.pc + 4)) := by
  simp only [exec, State.jumpAligned, h, ite_true, Option.map_some]
theorem exec_jalr (s : State) rd rs1 off (h : ((s.getReg rs1 + off) &&& ~~~1).toNat % 4 = 0) :
    exec s (.jalr rd rs1 off) = some ((s.setPC ((s.getReg rs1 + off) &&& ~~~1)).setReg rd (s.pc + 4)) := by
  simp only [exec, State.jumpAligned, h, ite_true, Option.map_some]
/-- `jalr` with offset 0 (e.g. `ret`) to an aligned register value. -/
theorem exec_jalr0 (s : State) rd rs1 (h : (s.getReg rs1).toNat % 4 = 0) :
    exec s (.jalr rd rs1 0#32) = some ((s.setPC (s.getReg rs1)).setReg rd (s.pc + 4)) := by
  have e : s.getReg rs1 &&& ~~~1 = s.getReg rs1 := by have := and_not_one_of_aligned _ h; simpa using this
  simp only [exec, State.jumpAligned, BitVec.add_zero, e, h, ite_true, Option.map_some]

theorem exec_branch_t (s : State) c rs1 rs2 off (h : c.holds (s.getReg rs1) (s.getReg rs2) = true)
    (ha : (s.pc + off).toNat % 4 = 0) : exec s (.branch c rs1 rs2 off) = some (s.setPC (s.pc + off)) := by
  simp only [exec, h, ite_true, State.jumpAligned, ha]
theorem exec_branch_f (s : State) c rs1 rs2 off (h : c.holds (s.getReg rs1) (s.getReg rs2) = false) :
    exec s (.branch c rs1 rs2 off) = some s.nextInstr := by
  simp only [exec, h, Bool.false_eq_true, ite_false]

theorem exec_load (s : State) n sg rd rs1 off (hrd : ¬ rd = 0) (ha : aligned (s.getReg rs1 + off) n)
    (hr : readable (s.getReg rs1 + off) n) :
    exec s (.load n sg rd rs1 off) = some (s.setReg rd
      (if sg then ((read s.mem (s.getReg rs1 + off) n).setWidth (8 * n)).signExtend 32 else read s.mem (s.getReg rs1 + off) n)).nextInstr := by
  simp only [exec, hrd, ↓reduceIte]; split
  · rfl
  · rename_i h; exact absurd ⟨ha, hr⟩ h
theorem exec_load_x0 (s : State) n sg rs1 off : exec s (.load n sg 0 rs1 off) = some s.nextInstr := by
  simp only [exec, ↓reduceIte]
/-- `lw` is a signed load (funct3 bit 2 = 0, as in Sail); for a full word that changes nothing. -/
theorem sext_word (x : Word) : BitVec.signExtend 32 (BitVec.setWidth (8 * 4) x) = x := by
  simp [BitVec.signExtend_eq]
theorem exec_store (s : State) n rs2 rs1 off (ha : aligned (s.getReg rs1 + off) n) (hw : writable (s.getReg rs1 + off) n) :
    exec s (.store n rs2 rs1 off) = some (s.store (s.getReg rs1 + off) (s.getReg rs2) n).nextInstr := by
  simp only [exec]; split
  · rfl
  · rename_i h; exact absurd ⟨ha, hw⟩ h

/-- A field operation (`mop.rr.N`); `mopVal` stays folded. -/
theorem exec_mop (s : State) op rd rs1 rs2 :
    exec s (.mop op rd rs1 rs2) = some (s.setReg rd (mopVal op (s.getReg rs1) (s.getReg rs2) (s.getReg rd))).nextInstr :=
  rfl

end RV

namespace RV
/-- Only the input read moves the input: the other state operations keep it. -/
theorem setReg_input (s : State) (r : Reg) (v : Word) : (s.setReg r v).input = s.input := rfl
theorem nextInstr_input (s : State) : s.nextInstr.input = s.input := rfl
theorem setPC_input (s : State) (t : Word) : (s.setPC t).input = s.input := rfl
theorem store_input (s : State) (a v : Word) (n : Nat) : (s.store a v n).input = s.input := rfl

attribute [rv_state] setReg_input nextInstr_input setPC_input store_input
attribute [rv_state] r_zero5 next_pc set_pc store_pc jump_pc set_mem next_mem store_mem jump_mem next_r store_r jump_r
  ite_true ite_false BitVec.ofNat_eq_ofNat BitVec.add_assoc BitVec.add_zero Bool.false_eq_true
attribute [rv_side] ROM_END RAM_END aligned writable readable and_not_one_of_aligned Cond.holds bne_iff_ne
  bne_eq_false_iff_eq beq_iff_eq beq_eq_false_iff_ne ne_eq
attribute [rv_exec high] read_write_rom read_write_off read_write_off0l read_write_off0r
attribute [rv_exec] step_ok Option.elim_some Option.bind_some read_write_disjoint read_write_same4
  exec_lui exec_auipc exec_opImm exec_op exec_jal exec_jalr0 exec_jalr exec_load exec_load_x0 sext_word exec_store alu
  exec_branch_t exec_branch_f exec_mop
end RV
