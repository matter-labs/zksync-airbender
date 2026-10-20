import Slop.RV.Jal
import Slop.RV.CopyRun

/-! # Control-flow tails of a block

One step at word `i` of a function's code (at `A`, in ROM) from any state whose ROM is the start's (`step_at`),
and the usual tails as one-step runs: `ret` (`run_ret`), a branch taken / not taken (`run_branch_t`,
`run_branch_f`), a call (`run_jal`). The pc arithmetic is done once, here. -/

namespace RV

/-- The step at word `i` of `code` (at `A`): it executes `decode w`, `w` the word there. -/
theorem step_at {S T : State} {A : Word} {code : List Word} (hc : CodeAt S A code) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * code.length ≤ ROM_END) (hT : ∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b)
    (i : Nat) (w : Word) (hw : code[i]? = some w) (hpc : T.pc = A + BitVec.ofNat 32 (4 * i)) :
    step T = (decode w).bind (exec T) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hw
  simp only [ROM_END] at hrom hT
  have h4 : T.pc.toNat + 4 ≤ 4194304 := by rw [hpc]; bv_omega
  refine step_fetch T _ (by rw [hpc]; bv_omega) (by simp only [ROM_END]; exact h4) ?_
  rw [read_congr T.mem S.mem _ 4 (fun j hj => hT _ (by bv_omega)), hpc]
  exact hc i hi

/-- The state after `ret` (`jalr x0, 0(ra)`). -/
def State.ret (T : State) : State := (T.setPC (T.getReg 1#5)).setReg 0#5 (T.pc + 4)

@[simp] theorem ret_pc (T : State) : T.ret.pc = T.getReg 1#5 := rfl
@[simp] theorem ret_mem (T : State) : T.ret.mem = T.mem := rfl
@[simp] theorem ret_input (T : State) : T.ret.input = T.input := rfl
@[simp] theorem ret_getReg (T : State) (r : Reg) : T.ret.getReg r = T.getReg r := by
  simp only [State.ret, r_set, jump_r]; split
  · next h => subst h; rfl
  · split
    · next h' h => subst h; exact absurd rfl h'
    · rfl

/-- `ret` at word `i`. -/
theorem run_ret {S T : State} {A : Word} {code : List Word} (hc : CodeAt S A code) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * code.length ≤ ROM_END) (hT : ∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b)
    (i : Nat) (hw : code[i]? = some 0x00008067#32) (hpc : T.pc = A + BitVec.ofNat 32 (4 * i))
    (hra : (T.getReg 1#5).toNat % 4 = 0) : run 1 T = some T.ret := by
  rw [run_succ, step_at hc hal hrom hT i _ hw hpc, show decode 0x00008067#32 = some (.jalr 0#5 1#5 0#32) from rfl,
    Option.bind_some, exec_jalr0 T _ _ hra]
  rfl

/-- A branch at word `i`, not taken. -/
theorem run_branch_f {S T : State} {A : Word} {code : List Word} (hc : CodeAt S A code) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * code.length ≤ ROM_END) (hT : ∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b)
    (i : Nat) (w : Word) (hw : code[i]? = some w) (hpc : T.pc = A + BitVec.ofNat 32 (4 * i))
    (c : Cond) (r1 r2 : Reg) (off : Word) (hd : decode w = some (.branch c r1 r2 off))
    (h : c.holds (T.getReg r1) (T.getReg r2) = false) : run 1 T = some T.nextInstr := by
  rw [run_succ, step_at hc hal hrom hT i _ hw hpc, hd, Option.bind_some, exec_branch_f _ _ _ _ _ h]; rfl

/-- A branch at word `i`, taken (to word `j`). -/
theorem run_branch_t {S T : State} {A : Word} {code : List Word} (hc : CodeAt S A code) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * code.length ≤ ROM_END) (hT : ∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b)
    (i : Nat) (w : Word) (hw : code[i]? = some w) (hpc : T.pc = A + BitVec.ofNat 32 (4 * i))
    (c : Cond) (r1 r2 : Reg) (off : Word) (hd : decode w = some (.branch c r1 r2 off))
    (h : c.holds (T.getReg r1) (T.getReg r2) = true) (j : Nat) (hj : 4 * i + off.toNat = 4 * j) :
    run 1 T = some (T.setPC (A + BitVec.ofNat 32 (4 * j))) := by
  have e : T.pc + off = A + BitVec.ofNat 32 (4 * j) := by rw [hpc]; bv_omega
  rw [run_succ, step_at hc hal hrom hT i _ hw hpc, hd, Option.bind_some,
    exec_branch_t _ _ _ _ _ h (by rw [e]; bv_omega), e]; rfl

/-- A call `jal ra, off` at word `i`, to `tgt`. -/
theorem run_jal {S T : State} {A : Word} {code : List Word} (hc : CodeAt S A code) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * code.length ≤ ROM_END) (hT : ∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b)
    (i : Nat) (w : Word) (hw : code[i]? = some w) (hpc : T.pc = A + BitVec.ofNat 32 (4 * i))
    (off : Word) (hd : decode w = some (.jal 1#5 off)) (tgt : Word)
    (ht : A + BitVec.ofNat 32 (4 * i) + off = tgt) (htal : tgt.toNat % 4 = 0) :
    run 1 T = some ((T.setPC tgt).setReg 1#5 (A + BitVec.ofNat 32 (4 * i + 4))) := by
  have e : T.pc + off = tgt := by rw [hpc, ht]
  have e4 : T.pc + 4 = A + BitVec.ofNat 32 (4 * i + 4) := by rw [hpc]; bv_omega
  rw [run_succ, step_at hc hal hrom hT i _ hw hpc, hd, Option.bind_some, exec_jal T _ _ (by rw [e]; exact htal),
    e, e4]; rfl

/-- The 13 callee-saved registers, one goal each. -/
theorem calleeSaved_all (P : Reg → Prop) (h2 : P 2#5) (h8 : P 8#5) (h9 : P 9#5) (h18 : P 18#5) (h19 : P 19#5)
    (h20 : P 20#5) (h21 : P 21#5) (h22 : P 22#5) (h23 : P 23#5) (h24 : P 24#5) (h25 : P 25#5) (h26 : P 26#5)
    (h27 : P 27#5) : ∀ i, calleeSaved i → P i := fun i hi => by
  rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> assumption

end RV
