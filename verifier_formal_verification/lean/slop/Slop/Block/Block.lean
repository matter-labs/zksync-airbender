import Slop.Sym.Meta
import Slop.RV.Input
import Slop.RV.Jal
import Slop.RV.CopyRun

/-! # Straight-line blocks and the steps around them

Three layers, all generic (no per-program arithmetic):

* `RV` — one step at a word of a function's code (`step_at`) and the tails that end a block as one-step runs:
  `ret` (`run_ret`), a branch taken / not taken (`run_branch_t`, `run_branch_f`), a jump-and-link (`run_jal`, any
  link register: `jal x0` is a plain jump). `x0_getReg`, `x0_pc` are the facts about a write to `x0`.
* `RV.Block` — `regs_same_range`: the registers of a range end as they started.
* `RV.Sym` — a block as one run (`block_at`, `block_ret`, `block_branch`) and the read-back facts of its final state:
  `Rel.reg_load`, `Rel.mem_nil`, the stored words (`Outs`: `out_const`, `out_load`) and memory outside a region
  (`Frames`: `out_frame`). -/

namespace RV

/-! ## One step -/

/-- Writing `x0` does nothing, and setting the pc changes no register. -/
theorem x0_getReg (S : State) (t v : Word) (r : Reg) : ((S.setPC t).setReg 0#5 v).getReg r = S.getReg r := by
  simp only [State.getReg, State.setReg, State.setPC]; split <;> simp_all

theorem x0_pc (S : State) (t v : Word) : ((S.setPC t).setReg 0#5 v).pc = t := rfl

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
@[simp] theorem ret_getReg (T : State) (r : Reg) : T.ret.getReg r = T.getReg r := x0_getReg T _ _ r

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
    (h : c.holds (T.getReg r1) (T.getReg r2) = true) (j : Nat) (hj : (4 * i + off.toNat) % 4294967296 = 4 * j) :
    run 1 T = some (T.setPC (A + BitVec.ofNat 32 (4 * j))) := by
  have e : T.pc + off = A + BitVec.ofNat 32 (4 * j) := by rw [hpc]; bv_omega
  rw [run_succ, step_at hc hal hrom hT i _ hw hpc, hd, Option.bind_some,
    exec_branch_t _ _ _ _ _ h (by rw [e]; bv_omega), e]; rfl

/-- A jump-and-link `jal rd, off` at word `i`, to `tgt` (`rd = x0`: a plain jump). -/
theorem run_jal {S T : State} {A : Word} {code : List Word} (hc : CodeAt S A code) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * code.length ≤ ROM_END) (hT : ∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b)
    (i : Nat) (w : Word) (hw : code[i]? = some w) (hpc : T.pc = A + BitVec.ofNat 32 (4 * i))
    (rd : Reg) (off : Word) (hd : decode w = some (.jal rd off)) (tgt : Word)
    (ht : A + BitVec.ofNat 32 (4 * i) + off = tgt) (htal : tgt.toNat % 4 = 0) :
    run 1 T = some ((T.setPC tgt).setReg rd (A + BitVec.ofNat 32 (4 * i + 4))) := by
  have e : T.pc + off = tgt := by rw [hpc, ht]
  have e4 : T.pc + 4 = A + BitVec.ofNat 32 (4 * i + 4) := by rw [hpc]; bv_omega
  rw [run_succ, step_at hc hal hrom hT i _ hw hpc, hd, Option.bind_some, exec_jal T rd _ (by rw [e]; exact htal),
    e, e4]; rfl

/-- `bne r, x0` / `beq r, x0` as a value test. -/
theorem holds_ne0 (a : Word) : Cond.holds .ne a (0#32) = !decide (a = 0#32) := by
  simp only [Cond.holds]; rfl

/-- The 13 callee-saved registers, one goal each. -/
theorem calleeSaved_all (P : Reg → Prop) (h2 : P 2#5) (h8 : P 8#5) (h9 : P 9#5) (h18 : P 18#5) (h19 : P 19#5)
    (h20 : P 20#5) (h21 : P 21#5) (h22 : P 22#5) (h23 : P 23#5) (h24 : P 24#5) (h25 : P 25#5) (h26 : P 26#5)
    (h27 : P 27#5) : ∀ i, calleeSaved i → P i := fun i hi => by
  rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> assumption

/-- Code at `A` is unchanged when memory is unchanged over its bytes. -/
theorem codeAt_of_mem_range {S S' : State} {A : Word} {code : List Word} (hc : CodeAt S A code)
    (hr : A.toNat + 4 * code.length ≤ 2 ^ 32)
    (h : ∀ a : Word, A.toNat ≤ a.toNat → a.toNat < A.toNat + 4 * code.length → S'.mem a = S.mem a) :
    CodeAt S' A code := by
  intro i hi
  rw [← hc i hi]
  apply read_congr
  intro j hj
  apply h <;> bv_omega

end RV

namespace RV.Block
open RV RV.Sym

/-- The registers whose numbers are in `[lo, hi]` end as they started (one `decide` over the range). -/
theorem regs_same_range {σ : SState} {S0 S : State} (instrs : List Instr)
    (hrun : symRun instrs initState = some σ) (h : Rel (ctxOf S0) σ S) (lo hi : Nat)
    (hl : (List.range' lo (hi + 1 - lo)).all (fun i => (σ.reg (BitVec.ofNat 5 i)).val == i) = true)
    (r : Reg) (h1 : lo ≤ r.toNat) (h2 : r.toNat ≤ hi) : S.getReg r = S0.getReg r := by
  have := List.all_eq_true.mp hl r.toNat (List.mem_range'_1.mpr ⟨h1, by omega⟩)
  simp only [beq_iff_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  exact h.reg_same instrs hrun r this

end RV.Block

namespace RV.Sym
open RV

/-! ## A block as one run -/

/-- The words a block stores, read back as nodes (`block_from`'s fourth result). -/
def Outs (σ : SState) (rs : List Region) (aps : List (Region × Region)) (S S' : State) : Prop :=
  ∀ b k, b < 32 → outOK σ rs aps b k = true →
    read S'.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 = σ.pool.val (ctxOf S) (outNode σ b k)

/-- Memory outside regions covering the stores is unchanged (`block_from`'s last result). -/
def Frames (σ : SState) (S S' : State) : Prop :=
  ∀ wr : List Region, writesIn wr σ = true → (∀ R ∈ wr, R.b < 32 ∧ R.Holds (ctxOf S) initPool) →
    ∀ a : Word, (∀ R ∈ wr, R.Outside S a) → S'.mem a = S.mem a

/-- Words `i … i+n` of `code` (at `A`, in ROM) as a straight-line block, from a state at word `i`: the machine runs
it to the state the symbolic state denotes; the input and ROM are unchanged. -/
theorem block_at (code : List Word) (i n : Nat) (instrs : List Instr) (σ : SState) (S : State) (A : Word)
    (rs : List Region) (aps : List (Region × Region))
    (hdec : ((code.drop i).take n).map decode = instrs.map some) (hrun : symRun instrs initState = some σ)
    (hn : i + n ≤ code.length) (hpc : S.pc = A + BitVec.ofNat 32 (4 * i)) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * code.length ≤ ROM_END) (hcode : CodeAt S A code)
    (hR : ∀ R ∈ rs, R.b < 32 ∧ R.Holds (ctxOf S) initPool)
    (hA : ∀ q ∈ aps, Apart (ctxOf S) initPool q.1 q.2)
    (hconds : σ.conds.all (checkCond rs aps) = true) :
    ∃ S', run n S = some S' ∧ S'.pc = A + BitVec.ofNat 32 (4 * (i + n)) ∧ S'.input = S.input ∧
      Rel (ctxOf S) σ S' ∧ (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧ Outs σ rs aps S S' ∧
      Frames σ S S' := by
  have hL : ((code.drop i).take n).length = n := by simp; omega
  simp only [ROM_END] at hrom
  have hc : CodeAt (S.withInput []) (A + BitVec.ofNat 32 (4 * i)) ((code.drop i).take n) :=
    codeAt_take (codeAt_drop (codeAt_mem_eq (withInput_mem S []) hcode) i (by omega)) n
  obtain ⟨S0, hrun0, hpc0, hrel0, hrom0, hout0, hfr0⟩ := block_from _ instrs σ (S.withInput []) _ rs aps hdec hrun
    (by rw [withInput_pc, hpc]) (by bv_omega) (by rw [hL]; simp only [ROM_END]; bv_omega) hc hR hA hconds
  rw [hL] at hrun0 hpc0
  obtain ⟨-, hl⟩ := run_lift n _ _ hrun0 rfl
  refine ⟨S0.withInput S.input, hl S.input, by rw [withInput_pc, hpc0]; bv_omega, rfl,
    hrel0.congr (fun r => withInput_getReg _ _ r) (withInput_mem _ _), fun b hb => hrom0 b hb,
    fun b k hb hk => hout0 b k hb hk, fun wr hw hwR a ha => hfr0 wr hw hwR a ha⟩

/-- A straight-line block (words `i … i+n` of `C`, at `A`) followed by `ret` (word `i+n`): `n+1` steps, to the
state after `ret`. `hra`: the block leaves `ra` aligned. -/
theorem block_ret {S : State} {A : Word} {C : List Word} (i n : Nat) (instrs : List Instr) (σ : SState)
    (rs : List Region) (aps : List (Region × Region))
    (hdec : ((C.drop i).take n).map decode = instrs.map some) (hrun : symRun instrs initState = some σ)
    (hn : i + n < C.length) (hpc : S.pc = A + BitVec.ofNat 32 (4 * i)) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * C.length ≤ ROM_END) (hcode : CodeAt S A C) (hw : C[i + n]? = some 0x00008067#32)
    (hR : ∀ R ∈ rs, R.b < 32 ∧ R.Holds (ctxOf S) initPool)
    (hA : ∀ q ∈ aps, Apart (ctxOf S) initPool q.1 q.2)
    (hconds : σ.conds.all (checkCond rs aps) = true)
    (hra : ∀ S', Rel (ctxOf S) σ S' → (S'.getReg 1#5).toNat % 4 = 0) :
    ∃ T, run (n + 1) S = some T ∧ T.pc = T.getReg 1#5 ∧ Rel (ctxOf S) σ T ∧
      (∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b) ∧ Outs σ rs aps S T ∧ Frames σ S T := by
  obtain ⟨S', hrun', hpc', -, hrel', hrom', hout', hfr'⟩ := block_at C i n instrs σ S A rs aps hdec hrun
    (by omega) hpc hal hrom hcode hR hA hconds
  have hr := run_ret hcode hal hrom hrom' (i + n) hw hpc' (hra S' hrel')
  exact ⟨S'.ret, run_trans hrun' hr, by rw [ret_pc, ret_getReg], hrel'.congr (ret_getReg S') rfl, hrom', hout', hfr'⟩

/-- A straight-line block (words `i … i+n` of `C`, at `A`) followed by a branch `c r1 r2 off` at word `i+n`, to the
word `j`, if taken. Its result is the state the branch leaves: `S'.setPC` the target if the condition holds, else
the next instruction. -/
theorem block_branch {S : State} {A : Word} {C : List Word} (i n : Nat) (instrs : List Instr) (σ : SState)
    (rs : List Region) (aps : List (Region × Region))
    (hdec : ((C.drop i).take n).map decode = instrs.map some) (hrun : symRun instrs initState = some σ)
    (hn : i + n < C.length) (hpc : S.pc = A + BitVec.ofNat 32 (4 * i)) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * C.length ≤ ROM_END) (hcode : CodeAt S A C) (bw : Word) (hw : C[i + n]? = some bw)
    (c : Cond) (r1 r2 : Reg) (off : Word) (hd : decode bw = some (.branch c r1 r2 off))
    (j : Nat) (hj : (4 * (i + n) + off.toNat) % 4294967296 = 4 * j)
    (hR : ∀ R ∈ rs, R.b < 32 ∧ R.Holds (ctxOf S) initPool)
    (hA : ∀ q ∈ aps, Apart (ctxOf S) initPool q.1 q.2)
    (hconds : σ.conds.all (checkCond rs aps) = true) :
    ∃ S', run (n + 1) S = some (if c.holds (S'.getReg r1) (S'.getReg r2) then
        S'.setPC (A + BitVec.ofNat 32 (4 * j)) else S'.nextInstr) ∧
      S'.pc = A + BitVec.ofNat 32 (4 * (i + n)) ∧ Rel (ctxOf S) σ S' ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧ Outs σ rs aps S S' ∧ Frames σ S S' := by
  obtain ⟨S', hrun', hpc', -, hrel', hrom', hout', hfr'⟩ := block_at C i n instrs σ S A rs aps hdec hrun
    (by omega) hpc hal hrom hcode hR hA hconds
  refine ⟨S', ?_, hpc', hrel', hrom', hout', hfr'⟩
  by_cases h : c.holds (S'.getReg r1) (S'.getReg r2) = true
  · rw [if_pos h]
    exact run_trans hrun' (run_branch_t hcode hal hrom hrom' (i + n) bw hw hpc' c r1 r2 off hd h j hj)
  · have h' : c.holds (S'.getReg r1) (S'.getReg r2) = false := by simpa using h
    rw [if_neg h]
    exact run_trans hrun' (run_branch_f hcode hal hrom hrom' (i + n) bw hw hpc' c r1 r2 off hd h')

/-- A register that ends as a 4-byte load from initial register `b` plus `k`. -/
theorem Rel.reg_load {σ : SState} {S0 S : State} (instrs : List Instr) (hrun : symRun instrs initState = some σ)
    (h : Rel (ctxOf S0) σ S) (r : Reg) (b : Nat) (k : Word) (hb : b < 32) (hi : (σ.reg r).val < σ.pool.len)
    (hn : nodeAt σ.pool (σ.reg r).val = .load 4 true b k) :
    S.getReg r = read S0.mem (S0.getReg (BitVec.ofNat 5 b) + k) 4 := by
  rw [(h.2.2.1 r).2]; exact load_val instrs σ hrun S0 _ b k true hb hi hn

/-- A block with no stores leaves memory as it was. -/
theorem Rel.mem_nil {σ : SState} {S0 S : State} (h : Rel (ctxOf S0) σ S) (hw : σ.writes = []) : S.mem = S0.mem := by
  rw [h.2.2.2.2, hw]; rfl

/-- A stored word that is a constant. -/
theorem out_const {σ : SState} {rs : List Region} {aps : List (Region × Region)} {S S' : State}
    (hwf : σ.pool.WF) (hout : Outs σ rs aps S S') (b : Nat) (k w : Word) (hb : b < 32)
    (hok : outOK σ rs aps b k = true) (hi : outNode σ b k < σ.pool.len)
    (hn : nodeAt σ.pool (outNode σ b k) = .const w) : read S'.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 = w := by
  rw [hout b k hb hok]; exact val_const hwf _ _ w hi hn

/-- A stored word that is a 4-byte load from initial register `b'` plus `k'`. -/
theorem out_load {σ : SState} {rs : List Region} {aps : List (Region × Region)} {S S' : State}
    (instrs : List Instr) (hrun : symRun instrs initState = some σ) (hout : Outs σ rs aps S S') (b : Nat) (k : Word)
    (b' : Nat) (k' : Word) (hb : b < 32) (hb' : b' < 32) (hok : outOK σ rs aps b k = true)
    (hi : outNode σ b k < σ.pool.len) (hn : nodeAt σ.pool (outNode σ b k) = .load 4 true b' k') :
    read S'.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 = read S.mem (S.getReg (BitVec.ofNat 5 b') + k') 4 := by
  rw [hout b k hb hok]; exact load_val instrs σ hrun S _ b' k' true hb' hi hn

/-- Memory outside one region `R` (`al = 1`) that covers all the stores is unchanged. -/
theorem out_frame {σ : SState} {S S' : State} (hfr : Frames σ S S') (R : Region) (hw : writesIn [R] σ = true)
    (hb : R.b < 32) (hR : R.Holds (ctxOf S) initPool) (a : Word) (ha : R.Outside S a) : S'.mem a = S.mem a :=
  hfr [R] hw (fun R' h => by simp only [List.mem_singleton] at h; subst h; exact ⟨hb, hR⟩) a
    (fun R' h => by simp only [List.mem_singleton] at h; subst h; exact ha)

end RV.Sym
