import Slop.RV.Merkle.MFrame
import Slop.RV.Tactic
import Slop.RV.CopyRun
import Slop.RV.Code.merkle_check
import Slop.RV.FsCheck.Blocks
import Slop.RV.Merkle.Contract
import Slop.RV.Input
import Slop.RV.CallW
import Slop.RV.Frame

/-! `merkle_check`, the loop (from word 46, `k ≥ 1` levels to go): read the side word and the sibling, call
`merkle_step` (any implementation of its contract), count down; at 0, the start of the end (word 68, `mc_exit`)
with the root of the whole path in `MERKLE.state`. By induction on `k`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

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
  have hcodeL : CodeAt L A Code.merkle_check := codeAt_of_rom hcode (by
    rw [show Code.merkle_check.length = 111 from rfl]; simp only [ROM_END] at hrom ⊢; omega) fr.rom
  -- the reads
  have hin' : L.input = (mcReads side sib).map (·.2) ++ (pathWords (path.drop (j + 1)) ++ rest) := by
    rw [hin, pathWords_drop path j hj, hpe, vec8_toList]; rfl
  have hR := run_reads (mcReads side sib) L _ hin' (by rw [hpc]; bv_omega)
    (by rw [hpc]; simp only [mcReads, List.length_cons, List.length_nil, ROM_END] at hrom ⊢; bv_omega)
    (fun i hi => by
      simp only [mcReads, List.length_cons, List.length_nil] at hi
      rw [hpc, show A + 184#32 + BitVec.ofNat 32 (4 * i) = A + BitVec.ofNat 32 (4 * (46 + i)) by bv_omega,
        hcodeL (46 + i) (by rw [show Code.merkle_check.length = 111 from rfl]; omega), ← getElem!_pos]
      interval_cases i <;> simp only [mcReads, List.getElem_cons_succ, List.getElem_cons_zero] <;> decide +kernel)
  rw [readsTo_withInput_comm] at hR
  apply run_of_run L _ _ _ hR
  obtain ⟨L', hL'⟩ : ∃ L', L' = L.withInput (pathWords (path.drop (j + 1)) ++ rest) := ⟨_, rfl⟩
  rw [← hL']
  have pc' : L'.pc = A + 184#32 := by rw [hL', withInput_pc, hpc]
  have m' : L'.mem = L.mem := by rw [hL', withInput_mem]
  have g' : ∀ r, L'.getReg r = L.getReg r := fun r => by rw [hL', withInput_getReg]
  have in' : L'.input = pathWords (path.drop (j + 1)) ++ rest := by rw [hL', withInput_input]
  have hcodeL' : CodeAt L' A Code.merkle_check := fun i h => by rw [m']; exact hcodeL i h
  unfold mcReads
  simp only [readsTo.eq_2, readsTo.eq_1]
  rv_code_facts hcodeL' Code.merkle_check
  obtain ⟨h2, h26, r0, r1, r2, r3, r4, r5, r6, r7, v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27,
    hmL, hromL⟩ := fr
  have hrom' := hrom
  have hsp0r := hsp0
  simp only [ROM_END] at hrom' hsp0r
  rv_steps 11 with pc', g', h2, h9, h26
  rv_cut with in', g'
  -- the sibling's stores, below `sp₀ - 52`
  obtain ⟨l8, hl8d⟩ : ∃ l : List (Nat × Word), l = [(84, sib[0]), (80, sib[1]), (76, sib[2]), (72, sib[3]),
      (68, sib[4]), (64, sib[5]), (60, sib[6]), (56, sib[7])] := ⟨_, rfl⟩
  have hMk : S.mem = frameWrites L'.mem (s0.getReg 2#5) l8 := by rw [cut_mem, hl8d]; rfl
  have hl8 : ∀ p ∈ l8, 56 ≤ p.1 ∧ p.1 ≤ 84 ∧ p.1 % 4 = 0 := by
    rw [hl8d]; intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  have hl8D : ∀ p ∈ l8, 56 ≤ p.1 ∧ p.1 ≤ 84 := fun p hp => ⟨(hl8 p hp).1, (hl8 p hp).2.1⟩
  have srom : ∀ b : Word, b.toNat < ROM_END → S.mem b = s0.mem b := fun b hb => by
    simp only [ROM_END] at hb
    rw [hMk, frameWrites_outside _ 56 84 (by decide) (by omega) _ _ _ hl8D (by omega), m',
      hromL b (by simp only [ROM_END]; omega)]
  apply run_callAtW_input hS S _ (by rw [cut_pc])
    (fun c hc => codeAt_of_rom (hcal c hc) (hcalr c hc) srom)
    ⟨by rw [show S.pc = A + 0x1bc#32 by rw [cut_pc]]; exact codeAt_of_rom hcS hSr srom,
      by rw [cut_pc]; bv_omega, by rw [cut_pc]; simp only [ROM_END] at hSr ⊢; bv_omega,
      by show (S.getReg 1#5).toNat % 4 = 0; rw [cut_r1]; bv_omega,
      by show (S.getReg 2#5).toNat % 16 = 0; rw [cut_r2, h2]; bv_omega,
      by show ROM_END + FS ≤ (S.getReg 2#5).toNat; rw [cut_r2, h2]; simp only [ROM_END]; bv_omega,
      by show (S.getReg 2#5).toNat ≤ RAM_END; rw [cut_r2, h2]; simp only [RAM_END]; bv_omega⟩
    (by
      simp only [merklePre, withInput_getReg, cut_r10, cut_r2, cut_r12, h9, h2, RAM_END]
      refine ⟨hMal, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega)
  intro U hpcU hpost hcsU hmemU hinU
  -- the node and the sibling `merkle_step` read
  have rd : ∀ b : Word, b.toNat + 4 ≤ 2 ^ 32 →
      b.toNat + 4 ≤ (s0.getReg 2#5).toNat - 84 ∨ (s0.getReg 2#5).toNat - 52 ≤ b.toNat →
      read S.mem b 4 = read L.mem b 4 := fun b hb1 hb => by
    rw [hMk, read_frameWrites_out _ 56 84 (by decide) (by omega) _ _ _ hl8D (by omega) hb1, m']
  have nodeS : readWords S.mem MERKLE 8 = readWords L.mem MERKLE 8 := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    exact rd _ (by rw [BitVec.toNat_add]; simp; omega) (by right; rw [BitVec.toNat_add]; simp; omega)
  have sibS : readWords S.mem (s0.getReg 2#5 + 4294967212#32) 8 = sib := by
    have hsp4 : (s0.getReg 2#5).toNat % 4 = 0 := by omega
    have lk : ∀ c, 56 ≤ c → c ≤ 84 → c % 4 = 0 →
        read S.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4 =
          frameLookup c (read L'.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4) l8 := fun c h1 h2 h3 => by
      rw [hMk]; exact read_frameWrites _ hsp4 _ _ c (fun p hp => ⟨by have := hl8 p hp; omega,
        by have := (hl8 p hp).2.1; omega, (hl8 p hp).2.2⟩) (by omega) (by omega) h3
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn, BitVec.add_assoc]
    interval_cases i
    · exact (lk 84 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d])
    · exact (lk 80 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d])
    · exact (lk 76 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d])
    · exact (lk 72 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d])
    · exact (lk 68 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d])
    · exact (lk 64 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d])
    · exact (lk 60 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d])
    · exact (lk 56 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d])
  have hnode' : readWords U.mem MERKLE 8 = merkleRoot leaf (path.take (j + 1)) := by
    have hp := hpost
    simp only [merklePost, withInput_getReg, withInput_mem, cut_r10, cut_r11, cut_r12] at hp
    rw [hp, sibS, nodeS, hnode, merkleRoot_take_succ leaf path j hj, hpe]
  -- what `merkle_step` kept: the frame's registers and words, memory outside its frame and `MERKLE`
  have sp' : (S.getReg 2#5).toNat = (s0.getReg 2#5).toNat - 96 := by rw [cut_r2, h2]; bv_omega
  have umem : ∀ a : Word, a.toNat + F < (s0.getReg 2#5).toNat ∨ (s0.getReg 2#5).toNat - 52 ≤ a.toNat →
      a.toNat < MERKLE.toNat ∨ MERKLE.toNat + len ≤ a.toNat → U.mem a = L.mem a := fun a ha hb => by
    rw [hmemU a (by rw [sp']; omega) (by rw [cut_r10]; exact hb), hMk,
      frameWrites_outside _ 56 84 (by decide) (by omega) _ _ _ hl8D (by omega), m']
  have uR : ∀ r : Reg, calleeSaved r → U.getReg r = L.getReg r := fun r hr => by
    rw [hcsU r hr]
    rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> assumption
  -- a saved word of the frame (offset `c` below `sp₀`) is kept
  have urd : ∀ c, 4 ≤ c → c ≤ 52 → ∀ v, read L.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4 = v →
      read U.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4 = v := fun c h1 h2 v h3 => by
    have ea := frame_addr (s0.getReg 2#5) c (by omega) (by omega)
    rw [← h3]
    exact read_congr _ _ _ _ (fun i hi => umem _ (by right; rw [BitVec.toNat_add, ea]; simp; omega)
      (by left; rw [BitVec.toNat_add, ea, show MERKLE.toNat = 0x1401100 from rfl]; simp; omega))
  have ufr : MFrame s0 F len root U :=
    ⟨(uR _ (by rv_callee_saved)).trans h2, (uR _ (by rv_callee_saved)).trans h26,
      (uR _ (by rv_callee_saved)).trans r0, (uR _ (by rv_callee_saved)).trans r1, (uR _ (by rv_callee_saved)).trans r2,
      (uR _ (by rv_callee_saved)).trans r3, (uR _ (by rv_callee_saved)).trans r4, (uR _ (by rv_callee_saved)).trans r5,
      (uR _ (by rv_callee_saved)).trans r6, (uR _ (by rv_callee_saved)).trans r7,
      urd 4 (by decide) (by decide) _ v1, urd 8 (by decide) (by decide) _ v8, urd 12 (by decide) (by decide) _ v9,
      urd 16 (by decide) (by decide) _ v18, urd 20 (by decide) (by decide) _ v19,
      urd 24 (by decide) (by decide) _ v20, urd 28 (by decide) (by decide) _ v21,
      urd 32 (by decide) (by decide) _ v22, urd 36 (by decide) (by decide) _ v23,
      urd 40 (by decide) (by decide) _ v24, urd 44 (by decide) (by decide) _ v25,
      urd 48 (by decide) (by decide) _ v26, urd 52 (by decide) (by decide) _ v27,
      fun a ha hb => by
        rw [umem a (by rcases ha with h | h <;> [left; right] <;> omega) hb]; exact hmL a ha hb,
      fun b hb => by
        rw [umem b (by left; simp only [ROM_END] at hb hsp0r; omega) (by left; simp only [ROM_END] at hb; bv_omega)]
        exact hromL b hb⟩
  have hcodeU : CodeAt U A Code.merkle_check := codeAt_of_rom hcode (by
    rw [show Code.merkle_check.length = 111 from rfl]; simp only [ROM_END] at hrom ⊢; omega) ufr.rom
  have hpcU' : U.pc = A + 264#32 := hpcU.trans cut_r1
  have u27 : U.getReg 27#5 = BitVec.ofNat 32 (k + 1) := (uR _ (by rv_callee_saved)).trans h27
  have u9 : U.getReg 9#5 = MERKLE := (uR _ (by rv_callee_saved)).trans h9
  have uin : U.input = pathWords (path.drop (j + 1)) ++ rest := hinU.trans cut_input
  clear hpost hmemU hcsU rd nodeS sibS umem urd hcodeL hcodeL' srom
  rv_code_facts hcodeU Code.merkle_check
  rv_steps 1 with hpcU', u27
  by_cases hk : k = 0
  · subst hk
    rv_steps 1 with hpcU', u27
    rv_cut with uin
    have fr' : MFrame s0 F len root S := ufr.of_eq (by rw [cut_mem]) (fun r hr => by
      rcases hr with h|h|h|h|h|h|h|h|h|h <;> subst h <;> assumption)
    have hn : readWords S.mem MERKLE 8 = merkleRoot leaf path := by
      rw [cut_mem, hnode', List.take_of_length_le (by omega)]
    exact ⟨0, S, rfl, by rw [cut_pc, hpcU']; bv_omega, fr',
      by rw [cut_input, show path.drop (j + 1) = [] from List.drop_eq_nil_of_le (by omega)]; rfl, hn⟩
  · have hs : BitVec.ofNat 32 (k + 1) + 4294967295#32 ≠ 0#32 := by bv_omega
    rv_steps 1 with hpcU', u27, hs
    rv_cut with uin
    have fr' : MFrame s0 F len root S := ufr.of_eq (by rw [cut_mem]) (fun r hr => by
      rcases hr with h|h|h|h|h|h|h|h|h|h <;> subst h <;> assumption)
    exact ih (j + 1) S (by omega) (by omega) (by rw [cut_pc]) fr' (by rw [cut_r9, u9])
      (by rw [cut_r27]; bv_omega) (by rw [cut_mem, hnode']) cut_input

end RV
