import Slop.Sym.Meta
import Slop.RV.Input
import Slop.RV.CopyRun

/-! # A straight-line block, packaged

`block_at`: words `i … i+n` of a function's code (at `A`) as one block — `block_from` without the take/drop,
length and alignment arithmetic, and with the input kept. Then its results read back, each by one lemma whose
side conditions are decided on the symbolic state's literal (`decide +kernel`):

* registers: `Rel.reg_load` (a 4-byte load from an initial register plus an offset), with `Rel.reg_same`,
  `Rel.reg_cst`, `Rel.reg_addr` (in `Sym/Func.lean`);
* stored words (`Outs`): `out_const`, `out_load`, `out_init`;
* memory: `Rel.mem_nil` (a block with no stores), `out_frame` (outside one region covering the stores). -/

namespace RV.Sym
open RV

theorem ctxOf_withInput (S : State) (t : List Word) : ctxOf (S.withInput t) = ctxOf S := rfl

theorem withInput_self (S : State) : S.withInput S.input = S := rfl

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

/-- A stored word that is the initial value of register `j`. -/
theorem out_init {σ : SState} {rs : List Region} {aps : List (Region × Region)} {S S' : State}
    (instrs : List Instr) (hrun : symRun instrs initState = some σ) (hout : Outs σ rs aps S S') (b : Nat) (k : Word)
    (j : Nat) (hb : b < 32) (hj : j < 32) (hok : outOK σ rs aps b k = true) (hn : outNode σ b k = j) :
    read S'.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 = S.getReg (BitVec.ofNat 5 j) := by
  rw [hout b k hb hok, hn]; exact val_init instrs σ hrun S j hj

/-- Memory outside one region `R` (`al = 1`) that covers all the stores is unchanged. -/
theorem out_frame {σ : SState} {S S' : State} (hfr : Frames σ S S') (R : Region) (hw : writesIn [R] σ = true)
    (hb : R.b < 32) (hR : R.Holds (ctxOf S) initPool) (a : Word) (ha : R.Outside S a) : S'.mem a = S.mem a :=
  hfr [R] hw (fun R' h => by simp only [List.mem_singleton] at h; subst h; exact ⟨hb, hR⟩) a
    (fun R' h => by simp only [List.mem_singleton] at h; subst h; exact ha)

end RV.Sym
