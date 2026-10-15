import Slop.Sym.Tree
import Slop.Sym.Block
import Slop.RV.CallW

/-! # A leaf function by the symbolic executor

A function whose code is a straight-line body followed by `ret`: if the symbolic run of the body succeeds, its side
conditions pass the checker, `ra` and the callee-saved registers end as they started, and every write is in the
stack frame or in the out-parameter, then the function returns (`ReturnsW`) with any `post` that holds of every
state the final symbolic state denotes. -/

namespace RV.Sym
open RV

/-- `ra` and the callee-saved registers. -/
def keptRegs : List Nat := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- Each kept register ends with its initial value. -/
def keptOK (σ : SState) : Bool := keptRegs.all fun i => (σ.reg (BitVec.ofNat 5 i)).val = i

/-- Each write is in one of the regions `wr`. -/
def writesIn (wr : List Region) (σ : SState) : Bool :=
  σ.writes.all fun w => wr.any fun R => R.covers w.base w.off w.n

/-- `ret`. -/
def retWord : Word := 0x00008067#32

theorem kept_val (σ : SState) (h : keptOK σ = true) (i : Reg) (hi : calleeSaved i ∨ i = 1#5) :
    (σ.reg i).val = i.toNat := by
  have key : ∀ j ∈ keptRegs, (σ.reg (BitVec.ofNat 5 j)).val = j := fun j hj => by
    simpa using List.all_eq_true.mp h j hj
  rcases hi with hi | rfl
  · rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> exact key _ (by decide)
  · exact key 1 (by decide)

theorem val_var (S : State) (p : Pool) (he : Ext (ctxOf S) initPool p) (i : Nat) (hi : i < 32) :
    p.val (ctxOf S) i = S.getReg (BitVec.ofNat 5 i) := by
  rw [he.2.2 i (by simpa [initPool] using hi)]; exact initPool_val S i hi

theorem region_ext {p p' : Pool} {c : Ctx} (he : Ext c p p') (R : Region) (hb : R.b < p.len) :
    R.Holds c p' ↔ R.Holds c p := by
  simp only [Region.Holds, he.2.2 _ hb]

theorem memOf_outside (c : Ctx) (p : Pool) (a : Word) : ∀ ws : List SWrite,
    (∀ w ∈ ws, a.toNat < (p.val c w.base + w.off).toNat ∨ (p.val c w.base + w.off).toNat + w.n ≤ a.toNat) →
    (∀ w ∈ ws, (p.val c w.base + w.off).toNat + w.n ≤ 2 ^ 32) → memOf c p ws a = c.m a
  | [], _, _ => rfl
  | w :: ws, h1, h2 => by
    simp only [memOf]
    rw [write_outside _ _ _ _ _ (h1 w (by simp)) (h2 w (by simp))]
    exact memOf_outside c p a ws (fun w' hw => h1 w' (by simp [hw])) (fun w' hw => h2 w' (by simp [hw]))

theorem Rel.congr {c : Ctx} {σ : SState} {S S' : State} (h : Rel c σ S) (hr : ∀ r, S'.getReg r = S.getReg r)
    (hm : S'.mem = S.mem) : Rel c σ S' :=
  ⟨h.1, h.2.1, fun r => ⟨(h.2.2.1 r).1, (hr r).trans (h.2.2.1 r).2⟩, h.2.2.2.1, hm.trans h.2.2.2.2⟩

/-- `a` is outside region `R` (around register `R.b` of `S`). -/
def Region.Outside (S : State) (R : Region) (a : Word) : Prop :=
  (a.toNat : Int) < ((S.getReg (BitVec.ofNat 5 R.b)).toNat : Int) + R.lo ∨
    ((S.getReg (BitVec.ofNat 5 R.b)).toNat : Int) + R.hi ≤ a.toNat

/-- A straight-line block from any state `S`: if its symbolic run succeeds and the side conditions pass the checker
(regions over `S`'s registers), the machine runs it; the final state is what the symbolic state denotes over `S`,
ROM is unchanged, stored words read back as nodes, and memory outside any region list covering the writes is
unchanged. -/
theorem block_from (code : List Word) (instrs : List Instr) (σ : SState) (S : State) (A : Word)
    (rs : List Region) (aps : List (Region × Region))
    (hdec : code.map decode = instrs.map some) (hrun : symRun instrs initState = some σ)
    (hpc : S.pc = A) (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * code.length ≤ ROM_END) (hcode : CodeAt S A code)
    (hR : ∀ R ∈ rs, R.b < 32 ∧ R.Holds (ctxOf S) initPool)
    (hA : ∀ q ∈ aps, Apart (ctxOf S) initPool q.1 q.2)
    (hconds : σ.conds.all (checkCond rs aps) = true) :
    ∃ S', run code.length S = some S' ∧ S'.pc = A + BitVec.ofNat 32 (4 * code.length) ∧ Rel (ctxOf S) σ S' ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧
      (∀ b k, b < 32 → outOK σ rs aps b k = true →
        read S'.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 = σ.pool.val (ctxOf S) (outNode σ b k)) ∧
      (∀ wr : List Region, writesIn wr σ = true → (∀ R ∈ wr, R.b < 32 ∧ R.Holds (ctxOf S) initPool) →
        ∀ a : Word, (∀ R ∈ wr, R.Outside S a) → S'.mem a = S.mem a) := by
  set c := ctxOf S
  obtain ⟨-, he, -⟩ := symRun_mono c instrs S initState σ (rel_init S) condsOK_init hrun
  have hlt : ∀ R ∈ rs, R.b < initPool.len := fun R hR' => by simpa [initPool] using (hR R hR').1
  have hR' : ∀ R ∈ rs, R.Holds c σ.pool := fun R hR'' => (region_ext he R (hlt R hR'')).mpr (hR R hR'').2
  have hA' : ∀ q ∈ aps, q.1 ∈ rs → q.2 ∈ rs → Apart c σ.pool q.1 q.2 := by
    intro q hq m₁ m₂
    have b₁ := hlt q.1 m₁; have b₂ := hlt q.2 m₂
    have := hA q hq
    simp only [Apart, he.2.2 _ b₁, he.2.2 _ b₂] at this ⊢; exact this
  obtain ⟨-, -, -, S', hrunB, hpc', hrel', hromB⟩ := run_block c code instrs S initState σ A hdec (rel_init S)
    condsOK_init hpc hal hrom hcode hrun (conds_hold c σ rs aps hR' hA' hconds)
  refine ⟨S', hrunB, hpc', hrel', hromB, fun b k hb hk => ?_, fun wr hwr hwR a ha => ?_⟩
  · rw [← val_var S σ.pool he b hb]; exact read_out c σ S' hrel' rs aps hR' hA' b k hk
  · rw [hrel'.2.2.2.2]
    have hw : ∀ w ∈ σ.writes, ((σ.pool.val c w.base + w.off).toNat : Int) + w.n ≤ RAM_END ∧
        (a.toNat < (σ.pool.val c w.base + w.off).toNat ∨ (σ.pool.val c w.base + w.off).toNat + w.n ≤ a.toNat) := by
      intro w hwm
      obtain ⟨R, hRm, hcov⟩ := List.any_eq_true.mp (List.all_eq_true.mp hwr w hwm)
      have hRb := (hwR R hRm).1
      have hRh : R.Holds c σ.pool :=
        (region_ext he R (by simpa [initState, initPool] using hRb)).mpr (hwR R hRm).2
      obtain ⟨-, b2, b3⟩ := covers_bounds c σ.pool R hRh w.base w.off w.n hcov
      have hv := val_var S σ.pool he R.b hRb
      have hout := ha R hRm
      simp only [Region.covers, Bool.and_eq_true, decide_eq_true_eq] at hcov
      simp only [Region.Outside] at hout
      rw [hv] at b3
      refine ⟨b2, ?_⟩
      omega
    exact memOf_outside c σ.pool a σ.writes (fun w hwm => (hw w hwm).2)
      (fun w hwm => by have := (hw w hwm).1; simp only [RAM_END] at this; omega)

/-- A register that ends as a folded constant holds it. -/
theorem Rel.reg_cst {c : Ctx} {σ : SState} {S : State} (h : Rel c σ S) (r : Reg) (w : Word)
    (hw : (σ.reg r).cst = some w) : S.getReg r = w :=
  ((h.2.2.1 r).2).trans ((h.2.2.1 r).1.2.2.2 w hw)

/-- A register that ends as the initial value of register `i`. -/
theorem Rel.reg_var {σ : SState} {S0 S : State} (instrs : List Instr) (hrun : symRun instrs initState = some σ)
    (h : Rel (ctxOf S0) σ S) (r : Reg) (i : Nat) (hi : i < 32) (hv : (σ.reg r).val = i) :
    S.getReg r = S0.getReg (BitVec.ofNat 5 i) := by
  obtain ⟨-, he, -⟩ := symRun_mono (ctxOf S0) instrs S0 initState σ (rel_init S0) condsOK_init hrun
  rw [(h.2.2.1 r).2, hv, val_var S0 σ.pool he i hi]

/-- A register that ends in address form `base + off`, `base` an initial register. -/
theorem Rel.reg_addr {σ : SState} {S0 S : State} (instrs : List Instr) (hrun : symRun instrs initState = some σ)
    (h : Rel (ctxOf S0) σ S) (r : Reg) (b : Nat) (k : Word) (hb : b < 32) (hv : (σ.reg r).base = b)
    (hk : (σ.reg r).off = k) : S.getReg r = S0.getReg (BitVec.ofNat 5 b) + k := by
  obtain ⟨-, he, -⟩ := symRun_mono (ctxOf S0) instrs S0 initState σ (rel_init S0) condsOK_init hrun
  rw [(h.2.2.1 r).2, (h.2.2.1 r).1.2.2.1, hv, hk, val_var S0 σ.pool he b hb]

/-- An initial register's node, after a run. -/
theorem val_init (instrs : List Instr) (σ : SState) (hrun : symRun instrs initState = some σ) (S : State) (i : Nat)
    (hi : i < 32) : σ.pool.val (ctxOf S) i = S.getReg (BitVec.ofNat 5 i) :=
  val_var S σ.pool (symRun_mono (ctxOf S) instrs S initState σ (rel_init S) condsOK_init hrun).2.1 i hi

/-- A register that ends as its own initial value. -/
theorem Rel.reg_same {σ : SState} {S0 S : State} (instrs : List Instr) (hrun : symRun instrs initState = some σ)
    (h : Rel (ctxOf S0) σ S) (r : Reg) (hv : (σ.reg r).val = r.toNat) : S.getReg r = S0.getReg r := by
  rw [h.reg_var instrs hrun r r.toNat r.isLt hv]; simp

theorem codeAt_take {S : State} {A : Word} {code : List Word} (h : CodeAt S A code) (n : Nat) :
    CodeAt S A (code.take n) := fun i hi => by
  have hi' : i < code.length := by simp at hi; omega
  simpa [List.getElem_take] using h i hi'

theorem codeAt_drop {S : State} {A : Word} {code : List Word} (h : CodeAt S A code) (n : Nat)
    (hr : A.toNat + 4 * code.length ≤ 2 ^ 32) : CodeAt S (A + BitVec.ofNat 32 (4 * n)) (code.drop n) := fun i hi => by
  have hi' : n + i < code.length := by simp at hi; omega
  rw [List.getElem_drop, ← h (n + i) hi']
  congr 1; rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

/-- A straight-line block followed by a call (`jal ra, off`): the state at the callee's entry is the block's final
state with `pc` at the target and `ra` the return address. -/
theorem block_jal (code : List Word) (instrs : List Instr) (σ : SState) (S : State) (A off : Word)
    (rs : List Region) (aps : List (Region × Region))
    (hdec : code.map decode = instrs.map some) (hrun : symRun instrs initState = some σ)
    (hpc : S.pc = A) (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * (code.length + 1) ≤ ROM_END)
    (hcode : CodeAt S A code) (jw : Word) (hjw : read S.mem (A + BitVec.ofNat 32 (4 * code.length)) 4 = jw)
    (hj : decode jw = some (.jal 1#5 off)) (htgt : (A + BitVec.ofNat 32 (4 * code.length) + off).toNat % 4 = 0)
    (hR : ∀ R ∈ rs, R.b < 32 ∧ R.Holds (ctxOf S) initPool)
    (hA : ∀ q ∈ aps, Apart (ctxOf S) initPool q.1 q.2)
    (hconds : σ.conds.all (checkCond rs aps) = true) :
    ∃ S', run (code.length + 1) S =
        some ((S'.setPC (A + BitVec.ofNat 32 (4 * code.length) + off)).setReg 1#5
          (A + BitVec.ofNat 32 (4 * code.length) + 4)) ∧
      Rel (ctxOf S) σ S' ∧ (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧
      (∀ b k, b < 32 → outOK σ rs aps b k = true →
        read S'.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 = σ.pool.val (ctxOf S) (outNode σ b k)) ∧
      (∀ wr : List Region, writesIn wr σ = true → (∀ R ∈ wr, R.b < 32 ∧ R.Holds (ctxOf S) initPool) →
        ∀ a : Word, (∀ R ∈ wr, R.Outside S a) → S'.mem a = S.mem a) := by
  obtain ⟨S', hrun', hpc', hrel', hrom', hout', hfr'⟩ := block_from code instrs σ S A rs aps hdec hrun hpc hal
    (by omega) hcode hR hA hconds
  refine ⟨S', ?_, hrel', hrom', hout', hfr'⟩
  have hw : read S'.mem S'.pc 4 = jw := by
    rw [read_congr S'.mem S.mem _ 4 (fun j hj => hrom' _ (by rw [hpc']; simp only [ROM_END] at *; bv_omega)), hpc',
      hjw]
  rw [run_add, hrun', Option.bind_some, run_succ,
    step_fetch S' jw (by rw [hpc']; bv_omega) (by rw [hpc']; simp only [ROM_END] at *; bv_omega) hw, hj,
    Option.bind_some, exec_jal S' _ _ (by rw [hpc']; exact htgt), hpc']
  rfl

theorem returnsW_of_sym (body : List Word) (instrs : List Instr) (σ : SState) (s : State) (frame len : Nat)
    (rs : List Region) (aps : List (Region × Region)) (post : State → State → Prop)
    (hdec : body.map decode = instrs.map some) (hrun : symRun instrs initState = some σ)
    (hcall : Call s (body ++ [retWord]) frame)
    (hR : ∀ R ∈ rs, R.b < 32 ∧ R.Holds (ctxOf s) initPool)
    (hA : ∀ q ∈ aps, Apart (ctxOf s) initPool q.1 q.2)
    (hconds : σ.conds.all (checkCond rs aps) = true) (hkept : keptOK σ = true)
    (hdst : ROM_END ≤ (s.getReg 10#5).toNat ∧ (s.getReg 10#5).toNat + len ≤ RAM_END)
    (hwr : writesIn [⟨2, -frame, 0, 1⟩, ⟨10, 0, len, 1⟩] σ = true)
    (hpost : ∀ S', Rel (ctxOf s) σ S' →
      (∀ b k, b < 32 → outOK σ rs aps b k = true →
        read S'.mem (s.getReg (BitVec.ofNat 5 b) + k) 4 = σ.pool.val (ctxOf s) (outNode σ b k)) → post s S') :
    ReturnsW s frame (s.getReg 10#5) len post := by
  set c := ctxOf s
  obtain ⟨hcode, hal, hrom, hra, -, hspl, hsph⟩ := hcall
  replace hspl : ROM_END + frame ≤ (s.getReg 2#5).toNat := hspl
  replace hsph : (s.getReg 2#5).toNat ≤ RAM_END := hsph
  replace hra : (s.getReg 1#5).toNat % 4 = 0 := hra
  have hlen : (body ++ [retWord]).length = body.length + 1 := by simp
  rw [hlen] at hrom
  have hcodeB : CodeAt s s.pc body := fun i hi => by
    have := hcode i (by simp; omega); simpa [List.getElem_append_left hi] using this
  obtain ⟨-, he, -⟩ := symRun_mono c instrs s initState σ (rel_init s) condsOK_init hrun
  have hlt : ∀ R ∈ rs, R.b < initPool.len := fun R hR' => by simpa [initPool] using (hR R hR').1
  have hR' : ∀ R ∈ rs, R.Holds c σ.pool := fun R hR'' => (region_ext he R (hlt R hR'')).mpr (hR R hR'').2
  have hA' : ∀ q ∈ aps, q.1 ∈ rs → q.2 ∈ rs → Apart c σ.pool q.1 q.2 := by
    intro q hq m₁ m₂
    have b₁ := hlt q.1 m₁; have b₂ := hlt q.2 m₂
    have := hA q hq
    simp only [Apart, he.2.2 _ b₁, he.2.2 _ b₂] at this ⊢; exact this
  obtain ⟨-, -, -, S', hrunB, hpc', hrel', hromB⟩ := run_block c body instrs s initState σ s.pc hdec (rel_init s)
    condsOK_init rfl hal (by omega) hcodeB hrun (conds_hold c σ rs aps hR' hA' hconds)
  have hreg : ∀ i : Reg, calleeSaved i ∨ i = 1#5 → S'.getReg i = s.getReg i := fun i hi => by
    rw [(hrel'.2.2.1 i).2, kept_val σ hkept i hi, val_var s σ.pool he _ i.isLt]; simp
  -- `ret`
  have hfetch : read S'.mem S'.pc 4 = retWord := by
    rw [read_congr S'.mem s.mem _ 4 (fun j hj => hromB _ (by rw [hpc']; bv_omega))]
    have := hcode body.length (by simp)
    simpa [hpc'] using this
  have hra' : (S'.getReg 1#5).toNat % 4 = 0 := by rw [hreg 1#5 (.inr rfl)]; exact hra
  set T := (S'.setPC (S'.getReg 1#5)).setReg 0#5 (S'.pc + 4)
  have hstep : step S' = some T := by
    rw [step_fetch S' retWord (by rw [hpc']; bv_omega) (by rw [hpc']; bv_omega) hfetch]
    simp only [retWord]
    rw [show decode 0x00008067#32 = some (.jalr 0#5 1#5 0#32) from rfl, Option.bind_some, exec_jalr0 S' _ _ hra']
  have hTr : ∀ r, T.getReg r = S'.getReg r := fun r => by
    simp only [T, State.getReg, State.setReg, State.setPC]; split <;> simp_all
  have hTm : T.mem = S'.mem := rfl
  refine ⟨body.length + 1, T, ?_, ?_, hpost T (hrel'.congr hTr hTm)
    (fun b k hb hk => by
      rw [← val_var s σ.pool he b hb]; exact read_out c σ T (hrel'.congr hTr hTm) rs aps hR' hA' b k hk), fun i hi => (hTr i).trans (hreg i (.inl hi)), ?_⟩
  · rw [run_add, hrunB, Option.bind_some, run_succ, hstep, Option.bind_some]; rfl
  · simp only [T, State.setReg, State.setPC]; exact hreg 1#5 (.inr rfl)
  · intro a ha hb
    replace ha : a.toNat + frame < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat := ha
    rw [hTm, hrel'.2.2.2.2]
    have hsp : σ.pool.val c 2 = s.getReg 2#5 := val_var s σ.pool he 2 (by decide)
    have ha0 : σ.pool.val c 10 = s.getReg 10#5 := val_var s σ.pool he 10 (by decide)
    have hRsp : Region.Holds c σ.pool ⟨2, -frame, 0, 1⟩ := by
      simp only [Region.Holds, hsp]; simp only [ROM_END, RAM_END] at *; omega
    have hRa0 : Region.Holds c σ.pool ⟨10, 0, len, 1⟩ := by
      simp only [Region.Holds, ha0]; simp only [ROM_END, RAM_END] at *; omega
    have hw : ∀ w ∈ σ.writes, (ROM_END : Int) ≤ ((σ.pool.val c w.base + w.off).toNat : Int) ∧
        ((σ.pool.val c w.base + w.off).toNat : Int) + w.n ≤ RAM_END ∧
        (a.toNat < (σ.pool.val c w.base + w.off).toNat ∨ (σ.pool.val c w.base + w.off).toNat + w.n ≤ a.toNat) := by
      intro w hwm
      have := List.any_eq_true.mp (List.all_eq_true.mp hwr w hwm)
      obtain ⟨R, hRm, hcov⟩ := this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRm
      rcases hRm with rfl | rfl
      · obtain ⟨b1, b2, b3⟩ := covers_bounds c σ.pool _ hRsp w.base w.off w.n hcov
        simp only [Region.covers, Bool.and_eq_true, decide_eq_true_eq] at hcov
        rw [hsp] at b3
        refine ⟨b1, b2, ?_⟩
        simp only [ROM_END, RAM_END] at *; omega
      · obtain ⟨b1, b2, b3⟩ := covers_bounds c σ.pool _ hRa0 w.base w.off w.n hcov
        simp only [Region.covers, Bool.and_eq_true, decide_eq_true_eq] at hcov
        rw [ha0] at b3
        refine ⟨b1, b2, ?_⟩
        simp only [ROM_END, RAM_END] at *; omega
    exact memOf_outside c σ.pool a σ.writes (fun w hwm => (hw w hwm).2.2)
      (fun w hwm => by have := (hw w hwm).2.1; simp only [RAM_END] at this; omega)

end RV.Sym
