import Slop.Sym.Meta
import Slop.RV.Jal

/-! # Control flow around straight-line blocks

`block_from` (Sym/Func.lean) runs a straight-line block. This file adds what ends a block — `ret`, a branch, a
plain jump — as single steps and packaged with the block (`block_ret`, `block_branch`), and the read-back facts of a
block's final state (`Rel`) as named lemmas: a register or a stored word that is a loaded word, a constant or an
initial register. All generic: no per-program arithmetic. -/

namespace RV.Block
open RV RV.Sym

/-! ## One step: `ret`, a branch, a jump -/

/-- The state after `ret` (`jalr x0, ra, 0`) or `j` (`jal x0, off`): only `pc` changes. -/
theorem x0_getReg (S : State) (t v : Word) (r : Reg) : ((S.setPC t).setReg 0#5 v).getReg r = S.getReg r := by
  simp only [State.getReg, State.setReg, State.setPC]; split <;> simp_all

theorem x0_mem (S : State) (t v : Word) : ((S.setPC t).setReg 0#5 v).mem = S.mem := rfl
theorem x0_pc (S : State) (t v : Word) : ((S.setPC t).setReg 0#5 v).pc = t := rfl

/-- `ret` at `pc`. -/
theorem run_ret (S : State) (hpc : S.pc.toNat % 4 = 0) (hrom : S.pc.toNat + 4 ≤ ROM_END)
    (hw : read S.mem S.pc 4 = retWord) (hra : (S.getReg 1#5).toNat % 4 = 0) :
    run 1 S = some ((S.setPC (S.getReg 1#5)).setReg 0#5 (S.pc + 4)) := by
  rw [run_succ, step_fetch S _ hpc hrom hw, retWord,
    show decode 0x00008067#32 = some (.jalr 0#5 1#5 0#32) from rfl, Option.bind_some, exec_jalr0 S _ _ hra]
  rfl

/-- `j off` (`jal x0, off`) at `pc`. -/
theorem run_j (S : State) (w off : Word) (hpc : S.pc.toNat % 4 = 0) (hrom : S.pc.toNat + 4 ≤ ROM_END)
    (hw : read S.mem S.pc 4 = w) (hd : decode w = some (.jal 0#5 off)) (ht : (S.pc + off).toNat % 4 = 0) :
    run 1 S = some ((S.setPC (S.pc + off)).setReg 0#5 (S.pc + 4)) := by
  rw [run_succ, step_fetch S _ hpc hrom hw, hd, Option.bind_some, exec_jal S _ _ ht]; rfl

/-- A conditional branch at `pc`: to `pc + off` if the condition holds, else on. -/
theorem run_branch (S : State) (w : Word) (c : Cond) (r1 r2 : Reg) (off : Word) (hpc : S.pc.toNat % 4 = 0)
    (hrom : S.pc.toNat + 4 ≤ ROM_END) (hw : read S.mem S.pc 4 = w) (hd : decode w = some (.branch c r1 r2 off))
    (ht : (S.pc + off).toNat % 4 = 0) :
    run 1 S = some (if c.holds (S.getReg r1) (S.getReg r2) then S.setPC (S.pc + off) else S.nextInstr) := by
  rw [run_succ, step_fetch S _ hpc hrom hw, hd, Option.bind_some]
  split
  · next h => rw [exec_branch_t _ _ _ _ _ h ht]; rfl
  · next h => rw [exec_branch_f _ _ _ _ _ (by simpa using h)]; rfl

/-- `bne r, x0` / `beq r, x0` as a value test. -/
theorem holds_ne0 (a : Word) : Cond.holds .ne a (0#32) = !decide (a = 0#32) := by
  simp only [Cond.holds]; rfl
theorem holds_eq0 (a : Word) : Cond.holds .eq a (0#32) = decide (a = 0#32) := by
  simp only [Cond.holds]; rfl

/-! ## A block, then `ret` or a branch -/

/-- The word after a block, fetched from the block's final state (ROM unchanged). -/
theorem fetch_after {S S' : State} {A : Word} {n : Nat} (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * (n + 1) ≤ ROM_END) (hpc' : S'.pc = A + BitVec.ofNat 32 (4 * n))
    (hromB : ∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) (w : Word)
    (hw : read S.mem (A + BitVec.ofNat 32 (4 * n)) 4 = w) :
    S'.pc.toNat % 4 = 0 ∧ S'.pc.toNat + 4 ≤ ROM_END ∧ read S'.mem S'.pc 4 = w := by
  have e : S'.pc.toNat = A.toNat + 4 * n := by rw [hpc']; simp only [ROM_END] at hrom; bv_omega
  refine ⟨by omega, by omega, ?_⟩
  rw [read_congr S'.mem S.mem _ 4 (fun j hj => hromB _ (by simp only [ROM_END] at hrom ⊢; bv_omega)), hpc', hw]

/-- A straight-line block followed by `ret`: the final state `T` is related to the symbolic state (`Rel`), at
`pc = ra`. `hra`: the block leaves `ra` aligned. -/
theorem block_ret (code : List Word) (instrs : List Instr) (σ : SState) (S : State) (A : Word)
    (rs : List Region) (aps : List (Region × Region))
    (hdec : code.map decode = instrs.map some) (hrun : symRun instrs initState = some σ)
    (hpc : S.pc = A) (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * (code.length + 1) ≤ ROM_END)
    (hcode : CodeAt S A code) (hjw : read S.mem (A + BitVec.ofNat 32 (4 * code.length)) 4 = retWord)
    (hR : ∀ R ∈ rs, R.b < 32 ∧ R.Holds (ctxOf S) initPool)
    (hA : ∀ q ∈ aps, Apart (ctxOf S) initPool q.1 q.2)
    (hconds : σ.conds.all (checkCond rs aps) = true)
    (hra : ∀ S', Rel (ctxOf S) σ S' → (S'.getReg 1#5).toNat % 4 = 0) :
    ∃ T, run (code.length + 1) S = some T ∧ T.pc = T.getReg 1#5 ∧ Rel (ctxOf S) σ T ∧
      (∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b) ∧
      (∀ b k, b < 32 → outOK σ rs aps b k = true →
        read T.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 = σ.pool.val (ctxOf S) (outNode σ b k)) ∧
      (∀ wr : List Region, writesIn wr σ = true → (∀ R ∈ wr, R.b < 32 ∧ R.Holds (ctxOf S) initPool) →
        ∀ a : Word, (∀ R ∈ wr, R.Outside S a) → T.mem a = S.mem a) := by
  obtain ⟨S', hrun', hpc', hrel', hrom', hout', hfr'⟩ := block_from code instrs σ S A rs aps hdec hrun hpc hal
    (by omega) hcode hR hA hconds
  obtain ⟨f1, f2, f3⟩ := fetch_after hal hrom hpc' hrom' _ hjw
  refine ⟨_, run_trans hrun' (run_ret S' f1 f2 f3 (hra S' hrel')), ?_, hrel'.congr (x0_getReg S' _ _) rfl,
    hrom', hout', hfr'⟩
  rw [x0_pc, x0_getReg]

/-- A straight-line block followed by a branch `c r1 r2 off`: the block's final state `S'` and the step after. -/
theorem block_branch (code : List Word) (instrs : List Instr) (σ : SState) (S : State) (A : Word)
    (rs : List Region) (aps : List (Region × Region))
    (hdec : code.map decode = instrs.map some) (hrun : symRun instrs initState = some σ)
    (hpc : S.pc = A) (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * (code.length + 1) ≤ ROM_END)
    (hcode : CodeAt S A code) (bw : Word) (hjw : read S.mem (A + BitVec.ofNat 32 (4 * code.length)) 4 = bw)
    (c : Cond) (r1 r2 : Reg) (off : Word) (hd : decode bw = some (.branch c r1 r2 off))
    (ht : (A + BitVec.ofNat 32 (4 * code.length) + off).toNat % 4 = 0)
    (hR : ∀ R ∈ rs, R.b < 32 ∧ R.Holds (ctxOf S) initPool)
    (hA : ∀ q ∈ aps, Apart (ctxOf S) initPool q.1 q.2)
    (hconds : σ.conds.all (checkCond rs aps) = true) :
    ∃ S', run (code.length + 1) S = some (if c.holds (S'.getReg r1) (S'.getReg r2) then
        S'.setPC (A + BitVec.ofNat 32 (4 * code.length) + off) else S'.nextInstr) ∧
      S'.pc = A + BitVec.ofNat 32 (4 * code.length) ∧ Rel (ctxOf S) σ S' ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧
      (∀ b k, b < 32 → outOK σ rs aps b k = true →
        read S'.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 = σ.pool.val (ctxOf S) (outNode σ b k)) ∧
      (∀ wr : List Region, writesIn wr σ = true → (∀ R ∈ wr, R.b < 32 ∧ R.Holds (ctxOf S) initPool) →
        ∀ a : Word, (∀ R ∈ wr, R.Outside S a) → S'.mem a = S.mem a) := by
  obtain ⟨S', hrun', hpc', hrel', hrom', hout', hfr'⟩ := block_from code instrs σ S A rs aps hdec hrun hpc hal
    (by omega) hcode hR hA hconds
  obtain ⟨f1, f2, f3⟩ := fetch_after hal hrom hpc' hrom' _ hjw
  refine ⟨S', ?_, hpc', hrel', hrom', hout', hfr'⟩
  have := run_trans hrun' (run_branch S' _ c r1 r2 off f1 f2 f3 hd (by rw [hpc']; exact ht))
  rwa [hpc'] at this

/-! ## Reading a block's final state -/

/-- A register that ends as a word loaded from `initial reg b + k`. -/
theorem reg_load {σ : SState} {S0 S : State} (instrs : List Instr) (hrun : symRun instrs initState = some σ)
    (h : Rel (ctxOf S0) σ S) (r : Reg) (b : Nat) (k : Word) (hb : b < 32) (hi : (σ.reg r).val < σ.pool.len)
    (hn : nodeAt σ.pool (σ.reg r).val = .load 4 true b k) :
    S.getReg r = read S0.mem (S0.getReg (BitVec.ofNat 5 b) + k) 4 := by
  rw [(h.2.2.1 r).2]; exact load_val _ _ hrun S0 _ b k true hb hi hn

/-- A stored word that reads back as a word loaded (before the block) from `initial reg b' + k'`. -/
theorem out_load {σ : SState} {S0 : State} {m : Word → BitVec 8} (instrs : List Instr)
    (hrun : symRun instrs initState = some σ) {b : Nat} {k : Word} {addr : Word}
    (hout : read m addr 4 = σ.pool.val (ctxOf S0) (outNode σ b k)) (b' : Nat) (k' : Word) (hb : b' < 32)
    (hi : outNode σ b k < σ.pool.len) (hn : nodeAt σ.pool (outNode σ b k) = .load 4 true b' k') :
    read m addr 4 = read S0.mem (S0.getReg (BitVec.ofNat 5 b') + k') 4 := by
  rw [hout]; exact load_val _ _ hrun S0 _ b' k' true hb hi hn

/-- A stored word that reads back as a constant. -/
theorem out_const {σ : SState} {S0 : State} {m : Word → BitVec 8} (hwf : σ.pool.WF) {b : Nat} {k : Word}
    {addr : Word} (hout : read m addr 4 = σ.pool.val (ctxOf S0) (outNode σ b k)) (w : Word)
    (hi : outNode σ b k < σ.pool.len) (hn : nodeAt σ.pool (outNode σ b k) = .const w) : read m addr 4 = w := by
  rw [hout]; exact val_const hwf _ _ w hi hn

/-- A stored word that reads back as an initial register. -/
theorem out_reg {σ : SState} {S0 : State} {m : Word → BitVec 8} (instrs : List Instr)
    (hrun : symRun instrs initState = some σ) {b : Nat} {k : Word} {addr : Word}
    (hout : read m addr 4 = σ.pool.val (ctxOf S0) (outNode σ b k)) (i : Nat) (hi : i < 32)
    (hn : outNode σ b k = i) : read m addr 4 = S0.getReg (BitVec.ofNat 5 i) := by
  rw [hout, hn]; exact val_init _ _ hrun S0 i hi

/-- Memory outside one region (around register `b` of `S`, bytes `[lo, hi)`) is unchanged, given the block's
frame clause and that all writes are in it. -/
theorem frame1 {σ : SState} {S S' : State} (b : Nat) (lo hi : Int)
    (hfr : ∀ wr : List Region, writesIn wr σ = true → (∀ R ∈ wr, R.b < 32 ∧ R.Holds (ctxOf S) initPool) →
      ∀ a : Word, (∀ R ∈ wr, R.Outside S a) → S'.mem a = S.mem a)
    (hw : writesIn [⟨b, lo, hi, 1⟩] σ = true) (hb : b < 32)
    (hH : (ROM_END : Int) ≤ ((S.getReg (BitVec.ofNat 5 b)).toNat : Int) + lo ∧
      ((S.getReg (BitVec.ofNat 5 b)).toNat : Int) + hi ≤ RAM_END)
    (a : Word) (ha : (a.toNat : Int) < ((S.getReg (BitVec.ofNat 5 b)).toNat : Int) + lo ∨
      ((S.getReg (BitVec.ofNat 5 b)).toNat : Int) + hi ≤ a.toNat) : S'.mem a = S.mem a := by
  apply hfr _ hw _ a
  · intro R hR; simp only [List.mem_singleton] at hR; subst hR; exact ha
  · intro R hR; simp only [List.mem_singleton] at hR; subst hR
    refine ⟨hb, ?_⟩
    simp only [Region.Holds, initPool_val _ _ hb]
    exact ⟨hH.1, hH.2, by decide, Nat.mod_one _⟩

end RV.Block

namespace RV.Block
open RV RV.Sym

/-- Registers whose numbers are in `l` end as they started (one `decide` over the list). -/
theorem regs_same {σ : SState} {S0 S : State} (instrs : List Instr) (hrun : symRun instrs initState = some σ)
    (h : Rel (ctxOf S0) σ S) (l : List Nat) (hl : l.all (fun i => (σ.reg (BitVec.ofNat 5 i)).val == i) = true)
    (r : Reg) (hr : r.toNat ∈ l) : S.getReg r = S0.getReg r := by
  have := List.all_eq_true.mp hl _ hr
  simp only [beq_iff_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  exact h.reg_same instrs hrun r this

/-- `regs_same` over a range `[lo, hi]`. -/
theorem regs_same_range {σ : SState} {S0 S : State} (instrs : List Instr)
    (hrun : symRun instrs initState = some σ) (h : Rel (ctxOf S0) σ S) (lo hi : Nat)
    (hl : (List.range' lo (hi + 1 - lo)).all (fun i => (σ.reg (BitVec.ofNat 5 i)).val == i) = true)
    (r : Reg) (h1 : lo ≤ r.toNat) (h2 : r.toNat ≤ hi) : S.getReg r = S0.getReg r :=
  regs_same instrs hrun h _ hl r (List.mem_range'_1.mpr ⟨h1, by omega⟩)

end RV.Block
