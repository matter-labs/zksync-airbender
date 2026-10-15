import Slop.Sym.Exec
import Slop.RV.Step

/-! # Soundness of the symbolic executor -/

namespace RV.Sym

variable (c : Ctx)

def SCond.Holds (σ : SState) : SCond → Prop
  | .aligned b k n => RV.aligned (σ.pool.val c b + k) n
  | .readable b k n => RV.readable (σ.pool.val c b + k) n
  | .writable b k n => RV.writable (σ.pool.val c b + k) n
  | .disj b₁ k₁ n₁ b₂ k₂ n₂ =>
    (σ.pool.val c b₁ + k₁).toNat + n₁ ≤ 2 ^ 32 ∧ (σ.pool.val c b₂ + k₂).toNat + n₂ ≤ 2 ^ 32 ∧
      ((σ.pool.val c b₁ + k₁).toNat + n₁ ≤ (σ.pool.val c b₂ + k₂).toNat ∨ (σ.pool.val c b₂ + k₂).toNat + n₂ ≤ (σ.pool.val c b₁ + k₁).toNat)

/-- The memory after the symbolic writes (newest first). -/
def memOf (p : Pool) : List SWrite → (Word → BitVec 8)
  | [] => c.m
  | w :: ws => write (memOf p ws) (p.val c w.base + w.off) (p.val c w.src.val) w.n

/-- A register value is a valid id whose address form is right. -/
def SReg.OK (p : Pool) (x : SReg) : Prop :=
  x.val < p.len ∧ x.base < p.len ∧ p.val c x.val = p.val c x.base + x.off

/-- The concrete state `S` is what the symbolic state `σ` denotes. -/
def Rel (σ : SState) (S : State) : Prop :=
  σ.pool.WF ∧ σ.regs.length = 32 ∧
  (∀ r : Reg, (σ.reg r).OK c σ.pool ∧ S.getReg r = σ.pool.val c (σ.reg r).val) ∧
  (∀ w ∈ σ.writes, w.base < σ.pool.len ∧ w.src.OK c σ.pool) ∧
  S.mem = memOf c σ.pool σ.writes

/-- All side conditions refer to existing ids. -/
def SCond.ids : SCond → List Nat
  | .aligned b _ _ => [b]
  | .readable b _ _ => [b]
  | .writable b _ _ => [b]
  | .disj b₁ _ _ b₂ _ _ => [b₁, b₂]

def CondsOK (σ : SState) : Prop := ∀ x ∈ σ.conds, ∀ j ∈ x.ids, j < σ.pool.len

/-- `p'` extends `p`: same values on the old ids. -/
def Ext (p p' : Pool) : Prop := p'.WF ∧ p.len ≤ p'.len ∧ ∀ j < p.len, p'.val c j = p.val c j

theorem Ext.refl (p : Pool) (h : p.WF) : Ext c p p := ⟨h, le_rfl, fun _ _ => by rfl⟩

theorem Ext.trans {p q r : Pool} (h1 : Ext c p q) (h2 : Ext c q r) : Ext c p r :=
  ⟨h2.1, le_trans h1.2.1 h2.2.1, fun j hj => (h2.2.2 j (lt_of_lt_of_le hj h1.2.1)).trans (h1.2.2 j hj)⟩

theorem SReg.OK.ext {p p' : Pool} {x : SReg} (he : Ext c p p') (h : x.OK c p) : x.OK c p' :=
  ⟨lt_of_lt_of_le h.1 he.2.1, lt_of_lt_of_le h.2.1 he.2.1, by rw [he.2.2 _ h.1, he.2.2 _ h.2.1]; exact h.2.2⟩

theorem memOf_ext {p p' : Pool} (he : Ext c p p') (ws : List SWrite)
    (hw : ∀ w ∈ ws, w.base < p.len ∧ w.src.OK c p) : memOf c p' ws = memOf c p ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h := hw w (by simp)
    simp only [memOf]
    rw [ih (fun w' hw' => hw w' (by simp [hw'])), he.2.2 _ h.1, he.2.2 _ h.2.1]

theorem SState.add_spec (σ σ' : SState) (n : Node) (i : Nat) (hw : σ.pool.WF) (h : σ.add n = some (σ', i)) :
    Ext c σ.pool σ'.pool ∧ i < σ'.pool.len ∧ σ'.pool.val c i = n.eval c (σ.pool.val c) ∧
      σ'.regs = σ.regs ∧ σ'.writes = σ.writes ∧ σ'.conds = σ.conds := by
  simp only [SState.add, bind, Option.bind] at h
  split at h
  · cases h
  · rename_i pi hpi
    obtain ⟨p', i'⟩ := pi
    cases h
    obtain ⟨h1, h2, h3, h4, h5⟩ := Pool.node_spec c _ _ _ _ hw hpi
    exact ⟨⟨h1, h2, h4⟩, h3, h5, rfl, rfl, rfl⟩

theorem reg_setReg (σ : SState) (rd r : Reg) (x : SReg) (hl : σ.regs.length = 32) :
    (σ.setReg rd x).reg r = if rd = 0 then σ.reg r else if r = rd then x else σ.reg r := by
  simp only [SState.setReg, SState.reg]
  split
  · rfl
  · rename_i h0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hr : r = rd
    · subst hr; simp [hl, r.isLt]
    · have : rd.toNat ≠ r.toNat := fun h => hr (BitVec.eq_of_toNat_eq h).symm
      simp [this, hr]

theorem setReg_regs_length (σ : SState) (rd : Reg) (x : SReg) (hl : σ.regs.length = 32) :
    (σ.setReg rd x).regs.length = 32 := by
  simp only [SState.setReg]; split <;> simp [hl]

theorem getReg_setReg (S : State) (rd r : Reg) (v : Word) :
    (S.setReg rd v).getReg r = if r = 0 then 0 else if r = rd then v else S.getReg r := by
  unfold State.getReg State.setReg; split_ifs <;> simp_all

/-- Writing a register. -/
theorem Rel.setReg {σ : SState} {S : State} (h : Rel c σ S) (rd : Reg) (x : SReg) (hx : x.OK c σ.pool) :
    Rel c (σ.setReg rd x) (S.setReg rd (σ.pool.val c x.val)) := by
  obtain ⟨hw, hl, hr, hws, hm⟩ := h
  have hp : (σ.setReg rd x).pool = σ.pool := by simp only [SState.setReg]; split <;> rfl
  have hwr : (σ.setReg rd x).writes = σ.writes := by simp only [SState.setReg]; split <;> rfl
  refine ⟨by rw [hp]; exact hw, setReg_regs_length σ rd x hl, fun r => ?_, by rw [hwr, hp]; exact hws,
    by rw [hwr, hp]; exact hm⟩
  rw [reg_setReg σ rd r x hl, getReg_setReg]
  simp only [hp]
  have h0v : σ.pool.val c (σ.reg 0).val = 0 := by have := (hr 0).2; simp [State.getReg] at this; exact this.symm
  by_cases h0 : rd = 0
  · subst h0; simp only [ite_true]
    refine ⟨(hr r).1, ?_⟩
    by_cases hr0 : r = 0
    · subst hr0; simp only [ite_true]; exact h0v.symm
    · simp only [hr0, ite_false]; exact (hr r).2
  · simp only [h0, ite_false]
    by_cases hr0 : r = 0
    · subst hr0
      have hne : (0 : Reg) ≠ rd := fun h => h0 h.symm
      simp only [hne, ite_false, ite_true]
      exact ⟨(hr 0).1, h0v.symm⟩
    · simp only [hr0, ite_false]
      split
      · exact ⟨hx, rfl⟩
      · exact hr r

/-- Growing the pool. -/
theorem Rel.ext {σ : SState} {S : State} (h : Rel c σ S) (p' : Pool) (he : Ext c σ.pool p') :
    Rel c { σ with pool := p' } S := by
  obtain ⟨hw, hl, hr, hws, hm⟩ := h
  refine ⟨he.1, hl, fun r => ⟨(hr r).1.ext c he, ?_⟩, fun w hw' => ⟨lt_of_lt_of_le (hws w hw').1 he.2.1,
    (hws w hw').2.ext c he⟩, ?_⟩
  · simp only [SState.reg] at *; rw [(hr r).2, he.2.2 _ (hr r).1.1]
  · simp only; rw [hm, memOf_ext c he _ hws]

/-- `read_write_off` for any sizes. -/
theorem read_write_off_n (m : Word → BitVec 8) (B k wk v : Word) (n wn : Nat) (h : n ≤ (wk - k).toNat ∧ wn ≤ (k - wk).toNat) :
    read (write m (B + wk) v wn) (B + k) n = read m (B + k) n := by
  apply read_congr; intro j hj; apply write_other; intro i hi; bv_omega

theorem resolve_spec (σ : SState) (b : Nat) (k : Word) (n : Nat) :
    ∀ (ws : List SWrite) (cs cs' : List SCond) (res : Option SReg), resolve b k n ws cs = some (res, cs') →
    (∀ w ∈ ws, w.base < σ.pool.len ∧ w.src.OK c σ.pool) → b < σ.pool.len →
    (∀ x ∈ cs, x ∈ cs') ∧ (∀ x ∈ cs', x ∈ cs ∨ ∀ j ∈ x.ids, j < σ.pool.len) ∧
    (∀ x, res = some x → x.OK c σ.pool) ∧
    ((∀ x ∈ cs', x.Holds c σ) →
      match res with
      | some x => n = 4 ∧ x.OK c σ.pool ∧ read (memOf c σ.pool ws) (σ.pool.val c b + k) n = σ.pool.val c x.val
      | none => read (memOf c σ.pool ws) (σ.pool.val c b + k) n = read c.m (σ.pool.val c b + k) n) := by
  intro ws
  induction ws with
  | nil =>
    intro cs cs' res h _ _
    simp only [resolve, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ h => h, fun x h => .inl h, fun _ h => by simp at h, fun _ => rfl⟩
  | cons w ws ih =>
    intro cs cs' res h hws hb
    have hw := hws w (by simp)
    have hws' : ∀ w' ∈ ws, w'.base < σ.pool.len ∧ w'.src.OK c σ.pool := fun w' h' => hws w' (by simp [h'])
    simp only [resolve] at h
    split at h
    · rename_i hbase
      split at h
      · rename_i hhit
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hoff, hn, hn4⟩ := hhit
        refine ⟨fun _ h => h, fun x h => .inl h, fun _ h => by injection h with h; subst h; exact hw.2, fun _ => ⟨hn4, hw.2, ?_⟩⟩
        simp only [memOf]; rw [hbase, hoff, hn, hn4]; exact read_write_same4 _ _ _
      · split at h
        · rename_i hd
          obtain ⟨h1, h2, h0, h3⟩ := ih cs cs' res h hws' hb
          refine ⟨h1, h2, h0, fun hh => ?_⟩
          have := h3 hh
          simp only [disjOff, decide_eq_true_eq] at hd
          revert this; cases res <;> intro this <;> simp only [memOf] at this ⊢ <;> rw [hbase, read_write_off_n _ _ _ _ _ _ _ hd] <;>
            exact this
        · cases h
    · obtain ⟨h1, h2, h0, h3⟩ := ih _ cs' res h hws' hb
      refine ⟨fun x hx => h1 x (by simp [hx]), fun x hx => ?_, h0, fun hh => ?_⟩
      · rcases h2 x hx with h | h
        · simp only [List.mem_cons] at h
          rcases h with rfl | h
          · right; intro j hj; simp only [SCond.ids, List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · exact hb
            · exact hw.1
          · exact .inl h
        · exact .inr h
      · have hd := hh (.disj b k n w.base w.off w.n) (h1 _ (by simp))
        simp only [SCond.Holds] at hd
        obtain ⟨hd1, hd2, hd3⟩ := hd
        have := h3 hh
        revert this; cases res <;> intro this <;> simp only [memOf] at this ⊢ <;>
          rw [read_write_disjoint _ _ _ _ _ _ (by omega) hd2 hd1] <;> exact this

theorem condsOK_of (σ σ' : SState) (h : CondsOK σ) (he : σ.pool.len ≤ σ'.pool.len) (hc : σ'.conds = σ.conds) :
    CondsOK σ' := fun x hx j hj => lt_of_lt_of_le (h x (hc ▸ hx) j hj) he

theorem commutes_alu (o : Op) (h : commutes o = true) (a b : Word) : alu o a b = alu o b a := by
  cases o <;> simp [commutes] at h <;> simp only [alu]
  · exact BitVec.add_comm _ _
  · exact BitVec.xor_comm _ _
  · exact BitVec.or_comm _ _
  · exact BitVec.and_comm _ _
  · exact BitVec.mul_comm _ _
  · rw [BitVec.mul_comm]

theorem opNode_eval (o : Op) (a b : Nat) (g : Nat → Word) :
    (opNode o a b).eval c g = alu o (g a) (g b) := by
  simp only [opNode]; split
  · rename_i h; simp only [Node.eval]; exact commutes_alu o (by simpa using h.1) _ _
  · rfl

/-- One register-writing step that adds one node: the shape of `lui`, `op`, … -/
theorem step_reg {σ σ1 : SState} {S : State} (hrel : Rel c σ S) (hcok : CondsOK σ) (n : Node) (v : Nat)
    (hadd : σ.add n = some (σ1, v)) (rd : Reg) (x : SReg) (hx : x.val = v) (hxok : x.OK c σ1.pool) :
    CondsOK (σ1.setReg rd x) ∧ Ext c σ.pool (σ1.setReg rd x).pool ∧
      (∀ y ∈ σ.conds, y ∈ (σ1.setReg rd x).conds) ∧
      Rel c (σ1.setReg rd x) (S.setReg rd (n.eval c (σ.pool.val c))).nextInstr := by
  obtain ⟨he, hv, hval, hregs, hws, hcs⟩ := SState.add_spec c σ σ1 n v hrel.1 hadd
  have hp : (σ1.setReg rd x).pool = σ1.pool := by simp only [SState.setReg]; split <;> rfl
  have hc : (σ1.setReg rd x).conds = σ1.conds := by simp only [SState.setReg]; split <;> rfl
  refine ⟨condsOK_of σ _ hcok (by rw [hp]; exact he.2.1) (by rw [hc, hcs]), by rw [hp]; exact he,
    fun y hy => by rw [hc, hcs]; exact hy, ?_⟩
  have hrel1 : Rel c σ1 S := by
    have := hrel.ext c σ1.pool he
    obtain ⟨a1, a2, a3, a4, a5⟩ := this
    exact ⟨a1, hregs ▸ a2, fun r => by simpa [SState.reg, hregs] using a3 r, fun w hw => a4 w (hws ▸ hw), hws ▸ a5⟩
  have := hrel1.setReg c rd x hxok
  rw [hx, hval] at this
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩

theorem eval_const (g : Nat → Word) (w : Word) : (Node.const w).eval c g = w := rfl

/-- After adding a node, everything still holds. -/
theorem add_rel {σ σ1 : SState} {S : State} (hrel : Rel c σ S) (hcok : CondsOK σ) (n : Node) (v : Nat)
    (hadd : σ.add n = some (σ1, v)) :
    Rel c σ1 S ∧ CondsOK σ1 ∧ Ext c σ.pool σ1.pool ∧ σ1.conds = σ.conds ∧ v < σ1.pool.len ∧
      σ1.pool.val c v = n.eval c (σ.pool.val c) ∧ ∀ r : Reg, σ1.reg r = σ.reg r := by
  obtain ⟨he, hv, hval, hregs, hws, hcs⟩ := SState.add_spec c σ σ1 n v hrel.1 hadd
  have hrel1 : Rel c σ1 S := by
    have := hrel.ext c σ1.pool he
    obtain ⟨a1, a2, a3, a4, a5⟩ := this
    exact ⟨a1, hregs ▸ a2, fun r => by simpa [SState.reg, hregs] using a3 r, fun w hw => a4 w (hws ▸ hw), hws ▸ a5⟩
  exact ⟨hrel1, condsOK_of σ σ1 hcok he.2.1 hcs, he, hcs, hv, hval, fun r => by simp [SState.reg, hregs]⟩

theorem holds_ext {p p' : Pool} (he : Ext c p p') (σ σ' : SState) (hp : σ.pool = p) (hp' : σ'.pool = p')
    (x : SCond) (hx : ∀ j ∈ x.ids, j < p.len) : x.Holds c σ' ↔ x.Holds c σ := by
  subst hp hp'
  cases x <;> simp only [SCond.ids, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx <;>
    simp only [SCond.Holds]
  · rw [he.2.2 _ hx]
  · rw [he.2.2 _ hx]
  · rw [he.2.2 _ hx]
  · rw [he.2.2 _ hx.1, he.2.2 _ hx.2]

theorem symStep_sound (σ σ' : SState) (S : State) (i : Instr) (hrel : Rel c σ S) (hcok : CondsOK σ)
    (hstep : symStep σ i = some σ') :
    CondsOK σ' ∧ Ext c σ.pool σ'.pool ∧ (∀ x ∈ σ.conds, x ∈ σ'.conds) ∧
    ∃ S', S'.pc = S.pc + 4 ∧ Rel c σ' S' ∧ ((∀ x ∈ σ'.conds, x.Holds c σ') → exec S i = some S' ∧
      ∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) := by
  cases i with
  | lui rd imm =>
    simp only [symStep, bind, Option.bind, pure] at hstep
    split at hstep
    · cases hstep
    · rename_i a ha; obtain ⟨σ1, v⟩ := a; cases hstep
      obtain ⟨hv, -⟩ := (SState.add_spec c σ σ1 _ v hrel.1 ha).2
      obtain ⟨h1, h2, h3, h4⟩ := step_reg c hrel hcok _ v ha rd ⟨v, v, 0⟩ rfl ⟨hv, hv, by simp⟩
      exact ⟨h1, h2, h3, (S.setReg rd imm).nextInstr, rfl, by simpa [eval_const] using h4, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
  | opImm o rd rs1 imm =>
    simp only [symStep, bind, Option.bind, pure] at hstep
    split at hstep
    · cases hstep
    · rename_i a ha; obtain ⟨σ1, ci⟩ := a
      simp only at hstep
      split at hstep
      · cases hstep
      · rename_i b hb; obtain ⟨σ2, v⟩ := b; cases hstep
        obtain ⟨r1, k1, e1, c1, -, vc, g1⟩ := add_rel c hrel hcok _ _ ha
        obtain ⟨r2, k2, e2, c2, hv, vv, g2⟩ := add_rel c r1 k1 _ _ hb
        have hrok : (σ.reg rs1).OK c σ2.pool := (hrel.2.2.1 rs1).1.ext c (e1.trans c e2)
        have hval : σ2.pool.val c v = alu o (S.getReg rs1) imm := by
          rw [vv]; simp only [Node.eval]
          rw [e1.2.2 _ (hrel.2.2.1 rs1).1.1, ← (hrel.2.2.1 rs1).2, vc, eval_const]
        have hxok : (addrForm o v (σ.reg rs1) imm).OK c σ2.pool := by
          cases o <;> simp only [addrForm] <;> first | exact ⟨hv, hv, by simp⟩ | skip
          refine ⟨hv, hrok.2.1, ?_⟩
          rw [hval, (hrel.2.2.1 rs1).2]; simp only [alu]
          rw [← e1.2.2 _ (hrel.2.2.1 rs1).1.1, ← e2.2.2 _ (lt_of_lt_of_le (hrel.2.2.1 rs1).1.1 e1.2.1),
            hrok.2.2, BitVec.add_assoc]
        obtain ⟨h1, h2, h3, h4⟩ := step_reg c r1 k1 _ v hb rd _ (by cases o <;> rfl) hxok
        refine ⟨h1, e1.trans c h2, fun y hy => h3 y (c1 ▸ hy), (S.setReg rd (alu o (S.getReg rs1) imm)).nextInstr,
          rfl, ?_, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
        convert h4 using 2
        rw [← vv, hval]
  | op o rd rs1 rs2 =>
    simp only [symStep, bind, Option.bind, pure] at hstep
    split at hstep
    · cases hstep
    · rename_i a ha; obtain ⟨σ1, v⟩ := a; cases hstep
      obtain ⟨-, -, -, -, hv, vv, -⟩ := add_rel c hrel hcok _ _ ha
      obtain ⟨h1, h2, h3, h4⟩ := step_reg c hrel hcok _ v ha rd ⟨v, v, 0⟩ rfl ⟨hv, hv, by simp⟩
      refine ⟨h1, h2, h3, (S.setReg rd (alu o (S.getReg rs1) (S.getReg rs2))).nextInstr, rfl, ?_,
        fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
      rw [opNode_eval, ← (hrel.2.2.1 rs1).2, ← (hrel.2.2.1 rs2).2] at h4; exact h4
  | mop o rd rs1 rs2 =>
    simp only [symStep, bind, Option.bind, pure] at hstep
    split at hstep
    · cases hstep
    · rename_i hrd
      split at hstep
      · cases hstep
      · rename_i a ha; obtain ⟨σ1, v⟩ := a; cases hstep
        obtain ⟨-, -, -, -, hv, vv, -⟩ := add_rel c hrel hcok _ _ ha
        obtain ⟨h1, h2, h3, h4⟩ := step_reg c hrel hcok _ v ha rd ⟨v, v, 0⟩ rfl ⟨hv, hv, by simp⟩
        refine ⟨h1, h2, h3, (S.setReg rd (mopVal o (S.getReg rs1) (S.getReg rs2) (S.getReg rd))).nextInstr, rfl, ?_,
          fun _ => ⟨by simp only [exec, hrd, ite_false], fun _ _ => rfl⟩⟩
        simp only [Node.eval] at h4
        rw [← (hrel.2.2.1 rs1).2, ← (hrel.2.2.1 rs2).2, ← (hrel.2.2.1 rd).2] at h4; exact h4
  | store n rs2 rs1 off =>
    simp only [symStep, pure] at hstep
    cases hstep
    obtain ⟨hw, hl, hr, hws, hm⟩ := hrel
    have hrok := (hr rs1).1
    have haddr : S.getReg rs1 + off = σ.pool.val c (σ.reg rs1).base + ((σ.reg rs1).off + off) := by
      rw [(hr rs1).2, hrok.2.2, BitVec.add_assoc]
    refine ⟨fun x hx j hj => ?_, Ext.refl c _ hw, fun x hx => by simp [hx],
      (S.store (S.getReg rs1 + off) (S.getReg rs2) n).nextInstr, by simp [State.nextInstr, State.store], ?_, fun hh => ?_⟩
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · simp only [SCond.ids, List.mem_singleton] at hj; subst hj; exact hrok.2.1
      · simp only [SCond.ids, List.mem_singleton] at hj; subst hj; exact hrok.2.1
      · exact hcok x hx j hj
    · refine ⟨hw, hl, fun r => hr r, fun w hw' => ?_, ?_⟩
      · simp only [List.mem_cons] at hw'
        rcases hw' with rfl | hw'
        · exact ⟨hrok.2.1, (hr rs2).1⟩
        · exact hws w hw'
      · simp only [State.nextInstr, State.store, memOf, hm, haddr, (hr rs2).2]
    · have ha := hh (.aligned (σ.reg rs1).base ((σ.reg rs1).off + off) n) (by simp)
      have hwr := hh (.writable (σ.reg rs1).base ((σ.reg rs1).off + off) n) (by simp)
      simp only [SCond.Holds] at ha hwr
      refine ⟨by simp only [exec, haddr]; rw [if_pos ⟨ha, hwr⟩], fun b hb => ?_⟩
      simp only [State.nextInstr, State.store]
      simp only [RV.writable, ROM_END, RAM_END] at hwr hb
      exact write_outside _ _ _ _ _ (by rw [haddr]; omega) (by rw [haddr]; omega)
  | load n sg rd rs1 off =>
    simp only [symStep, bind, Option.bind, pure] at hstep
    split at hstep
    · rename_i h0
      cases hstep
      exact ⟨hcok, Ext.refl c _ hrel.1, fun _ h => h, S.nextInstr, rfl, hrel,
        fun _ => ⟨by simp only [exec, h0, ite_true], fun _ _ => rfl⟩⟩
    · rename_i hrd
      have hrok := (hrel.2.2.1 rs1).1
      have haddr : S.getReg rs1 + off = σ.pool.val c (σ.reg rs1).base + ((σ.reg rs1).off + off) := by
        rw [(hrel.2.2.1 rs1).2, hrok.2.2, BitVec.add_assoc]
      split at hstep
      · cases hstep
      · rename_i res hres
        obtain ⟨res, cs'⟩ := res
        obtain ⟨g1, g2, g0, g3⟩ := resolve_spec c σ _ _ n σ.writes _ cs' res hres hrel.2.2.2.1 hrok.2.1
        have newok : ∀ x ∈ cs', ∀ j ∈ x.ids, j < σ.pool.len := by
          intro x hx j hj
          rcases g2 x hx with h | h
          · simp only [List.mem_cons] at h
            rcases h with rfl | rfl | h
            · simp only [SCond.ids, List.mem_singleton] at hj; subst hj; exact hrok.2.1
            · simp only [SCond.ids, List.mem_singleton] at hj; subst hj; exact hrok.2.1
            · exact hcok x h j hj
          · exact h j hj
        have hold : ∀ x ∈ σ.conds, x ∈ cs' := fun x hx => g1 x (by simp [hx])
        cases res with
        | some x =>
          simp only at hstep; cases hstep
          have hp : (σ.setReg rd x).pool = σ.pool := by simp only [SState.setReg]; split <;> rfl
          have hxok := g0 x rfl
          refine ⟨fun y hy j hj => by rw [hp]; exact newok y hy j hj, by rw [hp]; exact Ext.refl c _ hrel.1, hold,
            (S.setReg rd (σ.pool.val c x.val)).nextInstr, rfl, hrel.setReg c rd x hxok, fun hh => ?_⟩
          have hh' : ∀ y ∈ cs', y.Holds c σ := fun y hy => by
            have := hh y hy; simp only [SCond.Holds, hp] at this ⊢; cases y <;> exact this
          obtain ⟨hn4, -, hread⟩ := g3 hh'
          have hal := hh' (.aligned (σ.reg rs1).base ((σ.reg rs1).off + off) n) (g1 _ (by simp))
          have hrb := hh' (.readable (σ.reg rs1).base ((σ.reg rs1).off + off) n) (g1 _ (by simp))
          simp only [SCond.Holds] at hal hrb
          refine ⟨?_, fun _ _ => rfl⟩
          simp only [exec, haddr]; rw [if_neg hrd, if_pos ⟨hal, hrb⟩]
          have hv : (if sg then (read S.mem (σ.pool.val c (σ.reg rs1).base + ((σ.reg rs1).off + off)) n).setWidth (8 * n)
              |>.signExtend 32 else read S.mem (σ.pool.val c (σ.reg rs1).base + ((σ.reg rs1).off + off)) n) =
              σ.pool.val c x.val := by
            rw [hrel.2.2.2.2, hread]; subst hn4; cases sg <;> simp [sext_word]
          rw [hv]
        | none =>
          simp only at hstep
          split at hstep
          · cases hstep
          · rename_i a ha; obtain ⟨σ2, v⟩ := a; cases hstep
            obtain ⟨r2, k2, e2, c2, hv, vv, g2'⟩ := add_rel c hrel hcok _ _ ha
            have hp : (σ2.setReg rd ⟨v, v, 0⟩).pool = σ2.pool := by simp only [SState.setReg]; split <;> rfl
            refine ⟨fun y hy j hj => by rw [hp]; exact lt_of_lt_of_le (newok y hy j hj) e2.2.1,
              by rw [hp]; exact e2, hold, (S.setReg rd (σ2.pool.val c v)).nextInstr, rfl,
              r2.setReg c rd ⟨v, v, 0⟩ ⟨hv, hv, by simp⟩, fun hh => ?_⟩
            have hh' : ∀ y ∈ cs', y.Holds c σ := fun y hy =>
              (holds_ext c e2 σ _ rfl hp y (newok y hy)).mp (hh y hy)
            have hread := g3 hh'
            have hal := hh' (.aligned (σ.reg rs1).base ((σ.reg rs1).off + off) n) (g1 _ (by simp))
            have hrb := hh' (.readable (σ.reg rs1).base ((σ.reg rs1).off + off) n) (g1 _ (by simp))
            simp only [SCond.Holds] at hal hrb
            refine ⟨?_, fun _ _ => rfl⟩
            simp only [exec, haddr]; rw [if_neg hrd, if_pos ⟨hal, hrb⟩]
            have hval : σ2.pool.val c v = (if sg then (read S.mem (σ.pool.val c (σ.reg rs1).base +
                ((σ.reg rs1).off + off)) n).setWidth (8 * n) |>.signExtend 32
                else read S.mem (σ.pool.val c (σ.reg rs1).base + ((σ.reg rs1).off + off)) n) := by
              rw [vv, hrel.2.2.2.2, hread]; rfl
            rw [← hval]
  | auipc => simp [symStep] at hstep
  | jal => simp [symStep] at hstep
  | jalr => simp [symStep] at hstep
  | branch => simp [symStep] at hstep

end RV.Sym
