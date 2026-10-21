import Slop.RV.Merkle.MFrame
import Slop.RV.Merkle.Contract
import Slop.RV.Merkle.StartRuns
import Slop.RV.Code.finish_error
import Slop.Block.Block
import Slop.RV.CallW
import Slop.RV.Frame

/-! `merkle_check`, the loop (from word 46, `k ≥ 1` levels to go): read the side word and the sibling, call
`merkle_step` (any implementation of its contract), count down; at 0, the start of the end (word 68, `mc_exit`)
with the root of the whole path in `MERKLE.state`. By induction on `k`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

/-- The input words of a path (as `pathInput` reads them after the root and the depth). -/
def pathWords (path : List MerkleStep) : List Word := path.flatMap fun st => st.1 :: st.2.toList

theorem pathWords_drop (path : List MerkleStep) (j : Nat) (h : j < path.length) :
    pathWords (path.drop j) = path[j].1 :: path[j].2.toList ++ pathWords (path.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons h]; simp only [pathWords, List.flatMap_cons, List.cons_append]

theorem merkleRoot_take_succ (leaf : Vector Word 8) (path : List MerkleStep) (j : Nat) (h : j < path.length) :
    merkleRoot leaf (path.take (j + 1)) =
      if path[j].1 ≠ 0 then hash2 path[j].2 (merkleRoot leaf (path.take j))
      else hash2 (merkleRoot leaf (path.take j)) path[j].2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [merkleRoot, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A call to a function proven by `ImplementsAtW`, keeping track of the input: the contract is applied to the
state with the input empty (contracts do not mention it), and the run lifted (`run_lift`): the callee reads none. -/
theorem run_callAtW_input {entry : Word} {code : List Word} {callees : List (Word × List Word)} {frame len : Nat}
    {pre : State → Prop} {post : State → State → Prop} (hI : ImplementsAtW entry code callees frame pre len post)
    (X : State) (P : State → Prop) (hpc : X.pc = entry) (hcal : ∀ c ∈ callees, CodeAt X c.1 c.2)
    (hc : Call X code frame) (hpre : pre (X.withInput []))
    (h : ∀ U, U.pc = X.getReg 1#5 → post (X.withInput []) (U.withInput []) →
      (∀ i, calleeSaved i → U.getReg i = X.getReg i) →
      (∀ a : Word, a.toNat + frame < (X.getReg 2#5).toNat ∨ (X.getReg 2#5).toNat ≤ a.toNat →
        a.toNat < (X.getReg 10#5).toNat ∨ (X.getReg 10#5).toNat + len ≤ a.toNat → U.mem a = X.mem a) →
      U.input = X.input → ∃ m s', run m U = some s' ∧ P s') :
    ∃ m s', run m X = some s' ∧ P s' := by
  obtain ⟨n, U0, h1, h2, h3, h4, h5⟩ := hI (X.withInput []) (by rw [withInput_pc]; exact hpc)
    (fun c hc' => fun i hi => by rw [withInput_mem]; exact hcal c hc' i hi)
    (by obtain ⟨a, b, c, d, e, f, g⟩ := hc; exact ⟨fun i hi => by rw [withInput_mem, withInput_pc]; exact a i hi,
      by rw [withInput_pc]; exact b, by rw [withInput_pc]; exact c, by rw [withInput_getReg]; exact d,
      by rw [withInput_getReg]; exact e, by rw [withInput_getReg]; exact f, by rw [withInput_getReg]; exact g⟩) hpre
  obtain ⟨e0, lift⟩ := run_lift n _ U0 h1 rfl
  have hrun := lift X.input
  rw [show (X.withInput []).withInput X.input = X from rfl] at hrun
  refine run_of_run X _ n P hrun (h _ ?_ ?_ ?_ ?_ (by rw [withInput_input]))
  · rw [withInput_pc]; exact h2.trans (withInput_getReg _ _ _)
  · rw [show (U0.withInput X.input).withInput [] = U0 by rw [← e0]; rfl]; exact h3
  · intro i hi; rw [withInput_getReg, h4 i hi, withInput_getReg]
  · intro a ha hb
    rw [withInput_mem, h5 a (by rw [withInput_getReg]; exact ha) (by rw [withInput_getReg]; exact hb),
      withInput_mem]

theorem vec8_toList {α : Type} (v : Vector α 8) : v.toList = [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.length_toList] at h1
  interval_cases i <;> simp

/-- Words 46 … 54 of `merkle_check`: the side word into `a1`, the sibling into `a0, a2 … a7, t0`. -/
def mcReads (side : Word) (sib : Vector Word 8) : List (Reg × Word) :=
  [(11#5, side), (10#5, sib[0]), (12#5, sib[1]), (13#5, sib[2]), (14#5, sib[3]), (15#5, sib[4]), (16#5, sib[5]),
    (17#5, sib[6]), (5#5, sib[7])]

theorem readsTo_pc : ∀ (ps : List (Reg × Word)) (R : State),
    (readsTo R ps).pc = R.pc + BitVec.ofNat 32 (4 * ps.length)
  | [], _ => by simp [readsTo]
  | (rd, v) :: ps, R => by rw [readsTo, readsTo_pc ps, next_pc, set_pc, List.length_cons]; bv_omega

theorem readsTo_mem : ∀ (ps : List (Reg × Word)) (R : State), (readsTo R ps).mem = R.mem
  | [], _ => rfl
  | (_, _) :: ps, _ => (readsTo_mem ps _).trans rfl

/-- A register no read writes keeps its value. -/
theorem readsTo_getReg_other : ∀ (ps : List (Reg × Word)) (R : State) (r : Reg), (∀ p ∈ ps, p.1 ≠ r) →
    (readsTo R ps).getReg r = R.getReg r
  | [], _, _, _ => rfl
  | (rd, v) :: ps, R, r, h => by
    rw [readsTo, readsTo_getReg_other ps _ r (fun p hp => h p (List.mem_cons_of_mem _ hp)), next_r]
    have hne : ¬ r = rd := fun e => h (rd, v) List.mem_cons_self e.symm
    by_cases h0 : r = 0
    · subst h0; rw [r_zero, r_zero]
    · exact r_set_miss _ _ _ _ h0 hne

/-- A register read once holds the word read. -/
theorem readsTo_getReg : ∀ (ps : List (Reg × Word)) (R : State) (r : Reg) (v : Word), (ps.map (·.1)).Nodup →
    r ≠ 0 → (r, v) ∈ ps → (readsTo R ps).getReg r = v
  | [], _, _, _, _, _, h => by simp at h
  | (rd, w) :: ps, R, r, v, hn, h0, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rw [readsTo]
    rcases List.mem_cons.mp h with e | e
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rw [readsTo_getReg_other ps _ r (fun p hp e' => hn.1 ⟨p, hp, e'⟩), next_r, r_set_hit _ _ _ h0]
    · exact readsTo_getReg ps _ r v hn.2 h0 e

/-- The frame facts survive a change of memory away from the saved words and `MERKLE`'s `len` bytes, the
callee-saved registers kept. -/
theorem MFrame.of_mem {s0 E E' : State} {F len : Nat} {root : Vector Word 8} (h : MFrame s0 F len root E)
    (hsp0 : ROM_END + F ≤ (s0.getReg 2#5).toNat) (hsp0' : (s0.getReg 2#5).toNat ≤ 0x1400000)
    (hm : ∀ a : Word, a.toNat + F < (s0.getReg 2#5).toNat ∨ (s0.getReg 2#5).toNat - 52 ≤ a.toNat →
      a.toNat < MERKLE.toNat ∨ MERKLE.toNat + len ≤ a.toNat → E'.mem a = E.mem a)
    (hr : ∀ r : Reg, calleeSaved r → E'.getReg r = E.getReg r) : MFrame s0 F len root E' := by
  simp only [ROM_END] at hsp0
  have rd : ∀ c, 4 ≤ c → c ≤ 52 → ∀ v, read E.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4 = v →
      read E'.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4 = v := fun c h1 h2 v hv => by
    have ea := frame_addr (s0.getReg 2#5) c (by omega) (by omega)
    rw [← hv]
    exact read_congr _ _ _ _ (fun i hi => hm _ (by right; rw [BitVec.toNat_add, ea]; simp; omega)
      (by left; rw [BitVec.toNat_add, ea, show MERKLE.toNat = 0x1401100 from rfl]; simp; omega))
  obtain ⟨a, b, c, d, e, f, g, i, j, k, v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, m, rom⟩ := h
  have R : ∀ r, calleeSaved r → ∀ w, E.getReg r = w → E'.getReg r = w := fun r hr' w hw => (hr r hr').trans hw
  exact ⟨R _ (by rv_callee_saved) _ a, R _ (by rv_callee_saved) _ b, R _ (by rv_callee_saved) _ c,
    R _ (by rv_callee_saved) _ d, R _ (by rv_callee_saved) _ e, R _ (by rv_callee_saved) _ f,
    R _ (by rv_callee_saved) _ g, R _ (by rv_callee_saved) _ i, R _ (by rv_callee_saved) _ j,
    R _ (by rv_callee_saved) _ k, rd 4 (by decide) (by decide) _ v1, rd 8 (by decide) (by decide) _ v8,
    rd 12 (by decide) (by decide) _ v9, rd 16 (by decide) (by decide) _ v18, rd 20 (by decide) (by decide) _ v19,
    rd 24 (by decide) (by decide) _ v20, rd 28 (by decide) (by decide) _ v21, rd 32 (by decide) (by decide) _ v22,
    rd 36 (by decide) (by decide) _ v23, rd 40 (by decide) (by decide) _ v24, rd 44 (by decide) (by decide) _ v25,
    rd 48 (by decide) (by decide) _ v26, rd 52 (by decide) (by decide) _ v27,
    fun x hx hy => (hm x (by omega) hy).trans (m x hx hy),
    fun x hx => (hm x (by left; simp only [ROM_END] at hx; omega)
      (by left; simp only [ROM_END] at hx; rw [show MERKLE.toNat = 0x1401100 from rfl]; omega)).trans (rom x hx)⟩

theorem mc_loop (A : Word) (codeS : List Word) (calleesS : List (Word × List Word)) (FS al len : Nat)
    (hS : ImplementsAtW (A + 0x1bc#32) codeS calleesS FS (merklePre al len) len merklePost)
    (s0 : State) (F : Nat) (leaf root : Vector Word 8) (path : List MerkleStep) (rest : List Word)
    (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * 111 + 0x21c + 24 ≤ ROM_END)
    (hSr : (A + 0x1bc#32).toNat + 4 * codeS.length ≤ ROM_END)
    (hcalr : ∀ c ∈ calleesS, c.1.toNat + 4 * c.2.length ≤ ROM_END)
    (hcode : CodeAt s0 A Code.merkle_check) (_herr : CodeAt s0 (A + 0x3d4#32) Code.finish_error)
    (hcS : CodeAt s0 (A + 0x1bc#32) codeS) (hcal : ∀ c ∈ calleesS, CodeAt s0 c.1 c.2)
    (hMal : MERKLE.toNat % al = 0) (hlen : len ≤ 256) (hF : 96 + FS ≤ F) (hF2 : 112 ≤ F)
    (hsp0 : ROM_END + F ≤ (s0.getReg 2#5).toNat) (hsp0' : (s0.getReg 2#5).toNat ≤ 0x1400000)
    (hsp16 : (s0.getReg 2#5).toNat % 16 = 0) (hra : (s0.getReg 1#5).toNat % 4 = 0) (hd : path.length ≤ 32) :
    ∀ k j (L : State), 0 < k → j + k = path.length → L.pc = A + 184#32 → MFrame s0 F len root L →
      L.getReg 9#5 = MERKLE → L.getReg 27#5 = BitVec.ofNat 32 k →
      readWords L.mem MERKLE 8 = merkleRoot leaf (path.take j) → L.input = pathWords (path.drop j) ++ rest →
      ∃ m E, run m L = some E ∧ E.pc = A + 272#32 ∧ MFrame s0 F len root E ∧ E.input = rest ∧
        readWords E.mem MERKLE 8 = merkleRoot leaf path := by
  intro k
  induction k with
  | zero => intros; omega
  | succ k ih =>
  intro j L _ hjk hpc fr h9 h27 hnode hin
  have hj : j < path.length := by omega
  generalize hpe : path[j]'hj = st
  obtain ⟨side, sib⟩ := st
  have hL : Code.merkle_check.length = 111 := by decide +kernel
  have hromL : A.toNat + 4 * Code.merkle_check.length ≤ ROM_END := by
    rw [hL]; simp only [ROM_END] at hrom ⊢; omega
  have hcodeL : CodeAt L A Code.merkle_check := codeAt_of_rom hcode hromL fr.rom
  have hsp0r := hsp0
  simp only [ROM_END] at hsp0r
  -- the reads, words 46 … 54
  have hin' : L.input = (mcReads side sib).map (·.2) ++ (pathWords (path.drop (j + 1)) ++ rest) := by
    rw [hin, pathWords_drop path j hj, hpe, vec8_toList]; rfl
  have hR := run_reads (mcReads side sib) L _ hin' (by rw [hpc]; bv_omega)
    (by rw [hpc]; simp only [mcReads, List.length_cons, List.length_nil, ROM_END] at hrom ⊢; bv_omega)
    (fun i hi => by
      simp only [mcReads, List.length_cons, List.length_nil] at hi
      rw [hpc, show A + 184#32 + BitVec.ofNat 32 (4 * i) = A + BitVec.ofNat 32 (4 * (46 + i)) by bv_omega,
        hcodeL (46 + i) (by rw [hL]; omega), ← getElem!_pos]
      interval_cases i <;> simp only [mcReads, List.getElem_cons_succ, List.getElem_cons_zero] <;> decide +kernel)
  apply run_of_run L _ _ _ hR
  obtain ⟨X, hX⟩ : ∃ X, X = (readsTo L (mcReads side sib)).withInput (pathWords (path.drop (j + 1)) ++ rest) :=
    ⟨_, rfl⟩
  rw [← hX]
  have hXpc : X.pc = A + BitVec.ofNat 32 (4 * 55) := by
    rw [hX, withInput_pc, readsTo_pc, hpc]; simp only [mcReads, List.length_cons, List.length_nil]; bv_omega
  have hXm : X.mem = L.mem := by rw [hX, withInput_mem, readsTo_mem]
  have hXin : X.input = pathWords (path.drop (j + 1)) ++ rest := by rw [hX, withInput_input]
  have hXr : ∀ r v, (r, v) ∈ mcReads side sib → r ≠ 0 → X.getReg r = v := fun r v h h0 => by
    rw [hX, withInput_getReg]
    exact readsTo_getReg _ L r v (by simp only [mcReads, List.map_cons, List.map_nil]; decide) h0 h
  have hXk : ∀ r, calleeSaved r → X.getReg r = L.getReg r := fun r hr => by
    rw [hX, withInput_getReg]
    exact readsTo_getReg_other _ L r (by
      rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [mcReads])
  have hX2 : (X.getReg 2#5).toNat = (s0.getReg 2#5).toNat - 96 := by
    rw [hXk _ (by rv_callee_saved), fr.sp]; bv_omega
  have hcodeX : CodeAt X A Code.merkle_check := fun i h => by rw [hXm]; exact hcodeL i h
  -- the sibling's stores (below `sp`), the call's arguments (words 55 … 64), the call (65)
  obtain ⟨S1, hrun1, hpc1, hin1, hrel1, hrom1, hout1, hfr1⟩ := block_at Code.merkle_check 55 10 MSib.instrs
    MSib.σ X A [⟨2, 12, 44, 4⟩] [] MSib.dec MSib.run (by rw [hL]; omega) hXpc hal hromL hcodeX (by sym_side) (by simp)
    (by decide +kernel)
  have hjal := run_jal hcodeX hal hromL hrom1 65 0x0b8000ef#32 (by decide +kernel) hpc1 1#5 0xb8#32
    (by decide +kernel) (A + 0x1bc#32) (by bv_omega) (by bv_omega)
  apply run_of_run X _ _ _ (run_trans hrun1 hjal)
  obtain ⟨J, hJ⟩ : ∃ J, J = (S1.setPC (A + 0x1bc#32)).setReg 1#5 (A + BitVec.ofNat 32 (4 * 65 + 4)) := ⟨_, rfl⟩
  rw [← hJ]
  have hJm : J.mem = S1.mem := by rw [hJ]; rfl
  have hJr : ∀ r, r ≠ 1#5 → J.getReg r = S1.getReg r := fun r hr => by rw [hJ]; exact jal_getReg _ _ _ _ hr
  have hS1k : ∀ r, calleeSaved r → S1.getReg r = L.getReg r := fun r hr => by
    rw [Rel.reg_same MSib.instrs MSib.run hrel1 r (by
      rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide +kernel), hXk r hr]
  have ne1 : ∀ r, calleeSaved r → r ≠ 1#5 := fun r hr => by
    rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide
  have hJ2 : J.getReg 2#5 = s0.getReg 2#5 + 4294967200#32 :=
    (hJr _ (by decide)).trans ((hS1k _ (by rv_callee_saved)).trans fr.sp)
  have hJ10 : J.getReg 10#5 = MERKLE := by
    rw [hJr _ (by decide), Rel.reg_var MSib.instrs MSib.run hrel1 10#5 9 (by decide) (by decide +kernel)]
    exact (hXk _ (by rv_callee_saved)).trans h9
  have hJ11 : J.getReg 11#5 = side := by
    rw [hJr _ (by decide), Rel.reg_same MSib.instrs MSib.run hrel1 11#5 (by decide +kernel)]
    exact hXr _ _ (by simp [mcReads]) (by decide)
  have hJ12 : J.getReg 12#5 = X.getReg 2#5 + 12#32 := by
    rw [hJr _ (by decide), Rel.reg_addr MSib.instrs MSib.run hrel1 12#5 2 12#32 (by decide) (by decide +kernel)
      (by decide +kernel)]
  have hS1rom : ∀ b : Word, b.toNat < ROM_END → S1.mem b = s0.mem b := fun b hb =>
    (hrom1 b hb).trans (by rw [hXm]; exact fr.rom b hb)
  have mS1 : ∀ a : Word, a.toNat < (X.getReg 2#5).toNat + 12 ∨ (X.getReg 2#5).toNat + 44 ≤ a.toNat →
      S1.mem a = L.mem a := fun a ha => by
    rw [← hXm]
    exact out_frame hfr1 ⟨2, 12, 44, 1⟩ (by decide +kernel) (by decide) (by sym_side) a
      (by simp only [Region.Outside]; omega)
  apply run_callAtW_input hS J _ (by rw [hJ]; rfl)
    (fun c hc => codeAt_of_rom (hcal c hc) (hcalr c hc) (fun b hb => by rw [hJm]; exact hS1rom b hb))
    ⟨by rw [show J.pc = A + 0x1bc#32 by rw [hJ]; rfl]; exact codeAt_of_rom hcS hSr (fun b hb => by
        rw [hJm]; exact hS1rom b hb),
      by rw [show J.pc = A + 0x1bc#32 by rw [hJ]; rfl]; bv_omega,
      by rw [show J.pc = A + 0x1bc#32 by rw [hJ]; rfl]; simp only [ROM_END] at hSr ⊢; bv_omega,
      by show (J.getReg 1#5).toNat % 4 = 0; rw [hJ, jal_getReg1]; bv_omega,
      by show (J.getReg 2#5).toNat % 16 = 0; rw [hJ2]; bv_omega,
      by show ROM_END + FS ≤ (J.getReg 2#5).toNat; rw [hJ2]; simp only [ROM_END]; bv_omega,
      by show (J.getReg 2#5).toNat ≤ RAM_END; rw [hJ2]; simp only [RAM_END]; bv_omega⟩
    (by
      simp only [merklePre, withInput_getReg, hJ10, hJ12, hJ2, RAM_END]
      refine ⟨hMal, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega)
  intro U hpcU hpost hcsU hmemU hinU
  -- what `merkle_step` computed: the parent of the node and the sibling
  have sw : ∀ (k : Word) (r : Nat), r < 32 → outOK MSib.σ [⟨2, 12, 44, 4⟩] [] 2 k = true →
      outNode MSib.σ 2 k = r → read S1.mem (X.getReg 2#5 + k) 4 = X.getReg (BitVec.ofNat 5 r) :=
    fun k r hr hok hn => by
      rw [hout1 2 k (by decide) hok, hn]; exact val_init MSib.instrs MSib.σ MSib.run X r hr
  have sibS : readWords S1.mem (X.getReg 2#5 + 12#32) 8 = sib := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn, BitVec.add_assoc]
    interval_cases i
    · exact (sw _ 10 (by decide) (by decide +kernel) (by decide +kernel)).trans (hXr _ _ (by simp [mcReads]) (by decide))
    · exact (sw _ 12 (by decide) (by decide +kernel) (by decide +kernel)).trans (hXr _ _ (by simp [mcReads]) (by decide))
    · exact (sw _ 13 (by decide) (by decide +kernel) (by decide +kernel)).trans (hXr _ _ (by simp [mcReads]) (by decide))
    · exact (sw _ 14 (by decide) (by decide +kernel) (by decide +kernel)).trans (hXr _ _ (by simp [mcReads]) (by decide))
    · exact (sw _ 15 (by decide) (by decide +kernel) (by decide +kernel)).trans (hXr _ _ (by simp [mcReads]) (by decide))
    · exact (sw _ 16 (by decide) (by decide +kernel) (by decide +kernel)).trans (hXr _ _ (by simp [mcReads]) (by decide))
    · exact (sw _ 17 (by decide) (by decide +kernel) (by decide +kernel)).trans (hXr _ _ (by simp [mcReads]) (by decide))
    · exact (sw _ 5 (by decide) (by decide +kernel) (by decide +kernel)).trans (hXr _ _ (by simp [mcReads]) (by decide))
  have nodeS : readWords S1.mem MERKLE 8 = readWords L.mem MERKLE 8 := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    exact read_congr _ _ _ _ (fun i' hi' => mS1 _ (by right; rw [hX2]; simp; omega))
  have hnode' : readWords U.mem MERKLE 8 = merkleRoot leaf (path.take (j + 1)) := by
    have hp := hpost
    simp only [merklePost, withInput_getReg, withInput_mem, hJ10, hJ11, hJ12, hJm] at hp
    rw [hp, sibS, nodeS, hnode, merkleRoot_take_succ leaf path j hj, hpe]
  -- what `merkle_step` kept: the frame
  have ufr : MFrame s0 F len root U := MFrame.of_mem fr hsp0 hsp0' (fun a ha hb => by
      rw [hmemU a (by rw [hJ2]; bv_omega) (by rw [hJ10]; exact hb), hJm]
      exact mS1 a (by rw [hX2]; omega))
    (fun r hr => by rw [hcsU r hr, hJr r (ne1 r hr), hS1k r hr])
  have hcodeU : CodeAt U A Code.merkle_check := codeAt_of_rom hcode hromL ufr.rom
  have hpcU' : U.pc = A + BitVec.ofNat 32 (4 * 66) := by rw [hpcU, hJ, jal_getReg1]
  have u27 : U.getReg 27#5 = BitVec.ofNat 32 (k + 1) := by
    rw [hcsU _ (by rv_callee_saved), hJr _ (by decide), hS1k _ (by rv_callee_saved), h27]
  have u9 : U.getReg 9#5 = MERKLE := by
    rw [hcsU _ (by rv_callee_saved), hJr _ (by decide), hS1k _ (by rv_callee_saved), h9]
  have uin : U.input = pathWords (path.drop (j + 1)) ++ rest := by
    rw [hinU, hJ]; exact hin1.trans hXin
  -- the count down (word 66) and the loop's branch (67)
  obtain ⟨S2, hrun2, hpc2, hin2, hrel2, hrom2, -, -⟩ := block_at Code.merkle_check 66 1 MDec.instrs MDec.σ U A [] []
    MDec.dec MDec.run (by rw [hL]; omega) hpcU' hal hromL hcodeU (by simp) (by simp) (by decide +kernel)
  have m2 : S2.mem = U.mem := Rel.mem_nil hrel2 (by decide +kernel)
  have s27 : S2.getReg 27#5 = BitVec.ofNat 32 (k + 1) + 4294967295#32 := by
    rw [Rel.reg_addr MDec.instrs MDec.run hrel2 27#5 27 4294967295#32 (by decide) (by decide +kernel)
      (by decide +kernel)]; exact congrArg (· + 4294967295#32) u27
  have fr2 : MFrame s0 F len root S2 := ufr.of_eq m2 (fun r hr => by
    rcases hr with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      exact Rel.reg_same MDec.instrs MDec.run hrel2 _ (by decide +kernel))
  by_cases hk : k = 0
  · subst hk
    have hbf := run_branch_f hcodeU hal hromL hrom2 67 0xfa0d96e3#32 (by decide +kernel) hpc2 .ne 27#5 0#5
      0xffffffac#32 (by decide +kernel) (by rw [s27, r_zero5]; decide)
    refine ⟨1 + 1, S2.nextInstr, run_trans hrun2 hbf, by rw [next_pc, hpc2]; bv_omega,
      fr2.of_eq (next_mem _) (fun r _ => next_r _ r), ?_, ?_⟩
    · rw [nextInstr_input, hin2, uin, List.drop_eq_nil_of_le (by omega)]; rfl
    · rw [next_mem, m2, hnode', List.take_of_length_le (by omega)]
  · have hs : BitVec.ofNat 32 (k + 1) + 4294967295#32 ≠ 0#32 := by bv_omega
    have hbt := run_branch_t hcodeU hal hromL hrom2 67 0xfa0d96e3#32 (by decide +kernel) hpc2 .ne 27#5 0#5
      0xffffffac#32 (by decide +kernel) (by rw [s27, r_zero5, holds_ne0]; simp [hs]) 46 (by decide)
    apply run_of_run U _ _ _ (run_trans hrun2 hbt)
    exact ih (j + 1) _ (by omega) (by omega) (by rw [jump_pc])
      (fr2.of_eq (jump_mem _ _) (fun r _ => jump_r _ _ r))
      (by rw [jump_r, Rel.reg_same MDec.instrs MDec.run hrel2 _ (by decide +kernel), u9])
      (by rw [jump_r, s27]; bv_omega) (by rw [jump_mem, m2, hnode'])
      (by rw [show (S2.setPC (A + BitVec.ofNat 32 (4 * 46))).input = S2.input from rfl, hin2, uin])

end RV
