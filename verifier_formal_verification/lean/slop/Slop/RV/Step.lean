import Human.Call
import Slop.RV.Mem
import Slop.RV.Attr

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

/-- A call to a function proven by `Implements`: continue from any state it may return in. -/
theorem run_call {code : List Word} {frame : Nat} {post : State → State → Prop} (hI : Implements code frame post)
    (S : State) (P : State → Prop) (hc : Call S code frame)
    (h : ∀ S1, S1.pc = S.getReg 1 → post S S1 → (∀ i, calleeSaved i → S1.getReg i = S.getReg i) →
      (∀ a : Word, a.toNat + frame < (S.getReg 2).toNat ∨ (S.getReg 2).toNat ≤ a.toNat → S1.mem a = S.mem a) →
      ∃ m s', run m S1 = some s' ∧ P s') : ∃ m s', run m S = some s' ∧ P s' := by
  obtain ⟨n, S1, h1, h2, h3, h4, h5⟩ := hI S hc
  exact run_of_run S S1 n P h1 (h S1 h2 h3 h4 h5)

/-- A call to a function proven by `ImplementsAt` (fixed address, callees' code assumed). -/
theorem run_callAt {entry : Word} {code : List Word} {callees : List (Word × List Word)} {frame : Nat}
    {post : State → State → Prop} (hI : ImplementsAt entry code callees frame post)
    (S : State) (P : State → Prop) (hpc : S.pc = entry) (hcal : ∀ c ∈ callees, CodeAt S c.1 c.2)
    (hc : Call S code frame)
    (h : ∀ S1, S1.pc = S.getReg 1 → post S S1 → (∀ i, calleeSaved i → S1.getReg i = S.getReg i) →
      (∀ a : Word, a.toNat + frame < (S.getReg 2).toNat ∨ (S.getReg 2).toNat ≤ a.toNat → S1.mem a = S.mem a) →
      ∃ m s', run m S1 = some s' ∧ P s') : ∃ m s', run m S = some s' ∧ P s' := by
  obtain ⟨n, S1, h1, h2, h3, h4, h5⟩ := hI S hpc hcal hc
  exact run_of_run S S1 n P h1 (h S1 h2 h3 h4 h5)

/-- A word of a constant table (`CodeAt` of the table) at a symbolic index. -/
theorem table_read {s : State} {a : Word} {C : List Word} (h : CodeAt s a C) (i : Nat) (hi : i < C.length) :
    read s.mem (a + BitVec.ofNat 32 (4 * i)) 4 = C[i] := h i hi

/-- `ImplementsAt` with a precondition on the call state (e.g. argument values). -/
def ImplementsAtPre (entry : Word) (code : List Word) (callees : List (Word × List Word)) (frame : Nat)
    (pre : State → Prop) (post : State → State → Prop) : Prop :=
  ∀ s, s.pc = entry → (∀ c ∈ callees, CodeAt s c.1 c.2) → Call s code frame → pre s → Returns s frame post

theorem run_callAtPre {entry : Word} {code : List Word} {callees : List (Word × List Word)} {frame : Nat}
    {pre : State → Prop} {post : State → State → Prop} (hI : ImplementsAtPre entry code callees frame pre post)
    (S : State) (P : State → Prop) (hpc : S.pc = entry) (hcal : ∀ c ∈ callees, CodeAt S c.1 c.2)
    (hc : Call S code frame) (hpre : pre S)
    (h : ∀ S1, S1.pc = S.getReg 1 → post S S1 → (∀ i, calleeSaved i → S1.getReg i = S.getReg i) →
      (∀ a : Word, a.toNat + frame < (S.getReg 2).toNat ∨ (S.getReg 2).toNat ≤ a.toNat → S1.mem a = S.mem a) →
      ∃ m s', run m S1 = some s' ∧ P s') : ∃ m s', run m S = some s' ∧ P s' := by
  obtain ⟨n, S1, h1, h2, h3, h4, h5⟩ := hI S hpc hcal hc hpre
  exact run_of_run S S1 n P h1 (h S1 h2 h3 h4 h5)

/-- Reads outside a callee's frame see the memory from before the call. -/
theorem read_of_frame {m m' : Word → BitVec 8} {sp : Word} {F : Nat}
    (hmem : ∀ a : Word, a.toNat + F < sp.toNat ∨ sp.toNat ≤ a.toNat → m' a = m a) (b : Word) (k : Nat)
    (h : (b.toNat + k + F ≤ sp.toNat ∨ sp.toNat ≤ b.toNat) ∧ b.toNat + k ≤ 2 ^ 32) : read m' b k = read m b k := by
  apply read_congr
  intro j hj
  apply hmem
  bv_omega

/-- Code in ROM is not affected by stores (which only go to RAM). -/
theorem codeAt_store (s : State) (a : Word) (code : List Word) (b v : Word) (n : Nat)
    (hc : CodeAt s a code) (ha : a.toNat + 4 * code.length ≤ ROM_END) (hb : writable b n) :
    CodeAt (s.store b v n) a code := by
  intro i hi
  simp only [store_mem]
  rw [read_write_disjoint]
  · exact hc i hi
  all_goals simp only [writable, ROM_END, RAM_END] at *; bv_omega

/-- `CodeAt` on a raw memory. -/
def CodeMem (m : Word → BitVec 8) (a : Word) (code : List Word) : Prop :=
  ∀ i (h : i < code.length), read m (a + BitVec.ofNat 32 (4 * i)) 4 = code[i]

theorem codeMem_of_codeAt {s : State} {a code} (h : CodeAt s a code) : CodeMem s.mem a code := h

/-- Code in ROM is not affected by a store to RAM. -/
theorem codeMem_write {m : Word → BitVec 8} {a : Word} {code : List Word} (b v : Word) (n : Nat)
    (hc : CodeMem m a code) (ha : a.toNat + 4 * code.length ≤ ROM_END) (hb : writable b n) :
    CodeMem (write m b v n) a code := by
  intro i hi
  rw [read_write_disjoint]
  · exact hc i hi
  all_goals simp only [writable, ROM_END, RAM_END] at *; bv_omega

/-- Code (or a table) outside a callee's stack frame is not affected by the call. -/
theorem codeAt_of_frame {S1 : State} {m : Word → BitVec 8} {sp : Word} {F : Nat} {a : Word} {code : List Word}
    (hc : CodeMem m a code) (hmem : ∀ b : Word, b.toNat + F < sp.toNat ∨ sp.toNat ≤ b.toNat → S1.mem b = m b)
    (h : (a.toNat + 4 * code.length + F ≤ sp.toNat ∨ sp.toNat ≤ a.toNat) ∧ a.toNat + 4 * code.length ≤ 2 ^ 32) :
    CodeAt S1 a code := by
  intro i hi
  rw [read_of_frame hmem _ _ (by bv_omega)]
  exact hc i hi

/-- Code (or a table) is not affected by a store that does not overlap it. -/
theorem codeAt_store_disj (s : State) (a : Word) (code : List Word) (b v : Word) (n : Nat) (hc : CodeAt s a code)
    (h : b.toNat + n ≤ a.toNat ∨ a.toNat + 4 * code.length ≤ b.toNat) (ha : a.toNat + 4 * code.length ≤ 2 ^ 32)
    (hb : b.toNat + n ≤ 2 ^ 32) : CodeAt (s.store b v n) a code := by
  intro i hi
  simp only [store_mem]
  rw [read_write_disjoint _ _ _ _ _ _ (by bv_omega) hb (by bv_omega)]
  exact hc i hi

theorem codeMem_write_disj {m : Word → BitVec 8} {a : Word} {code : List Word} (b v : Word) (n : Nat)
    (hc : CodeMem m a code) (h : b.toNat + n ≤ a.toNat ∨ a.toNat + 4 * code.length ≤ b.toNat)
    (ha : a.toNat + 4 * code.length ≤ 2 ^ 32) (hb : b.toNat + n ≤ 2 ^ 32) : CodeMem (write m b v n) a code := by
  intro i hi
  rw [read_write_disjoint _ _ _ _ _ _ (by bv_omega) hb (by bv_omega)]
  exact hc i hi

theorem calleeSaved_cases (i : Reg) (h : calleeSaved i) :
    i = 2#5 ∨ i = 8#5 ∨ i = 9#5 ∨ i = 18#5 ∨ i = 19#5 ∨ i = 20#5 ∨ i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 ∨ i = 26#5 ∨
    i = 27#5 := by
  unfold calleeSaved at h; bv_omega

theorem codeAt_set (s : State) a code rd v (h : CodeAt s a code) : CodeAt (s.setReg rd v) a code := h
theorem codeAt_next (s : State) a code (h : CodeAt s a code) : CodeAt s.nextInstr a code := h
theorem codeAt_jump (s : State) a code t (h : CodeAt s a code) : CodeAt (s.setPC t) a code := h

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

/-- A field operation (`mop.rr.N`) with `rd ≠ x0`; `mopVal` stays folded. -/
theorem exec_mop (s : State) op rd rs1 rs2 (hrd : ¬ rd = 0) :
    exec s (.mop op rd rs1 rs2) = some (s.setReg rd (mopVal op (s.getReg rs1) (s.getReg rs2) (s.getReg rd))).nextInstr := by
  simp only [exec, hrd, ↓reduceIte]

end RV

namespace RV
attribute [rv_state] r_zero5 next_pc set_pc store_pc jump_pc set_mem next_mem store_mem jump_mem next_r store_r jump_r
  ite_true ite_false BitVec.ofNat_eq_ofNat BitVec.add_assoc BitVec.add_zero Bool.false_eq_true
attribute [rv_side] ROM_END RAM_END aligned writable readable and_not_one_of_aligned Cond.holds bne_iff_ne
  bne_eq_false_iff_eq beq_iff_eq beq_eq_false_iff_ne ne_eq
attribute [rv_exec high] read_write_rom read_write_off read_write_off0l read_write_off0r
attribute [rv_exec] step_ok Option.elim_some Option.bind_some read_write_disjoint read_write_same4
  exec_lui exec_auipc exec_opImm exec_op exec_jal exec_jalr0 exec_jalr exec_load exec_load_x0 sext_word exec_store alu
  exec_branch_t exec_branch_f exec_mop
end RV
