import Slop.RV.Merkle.Loop
import Slop.RV.Merkle.Exit

/-! `merkle_check(leaf)`, the whole function: the prologue, the root and the depth (9 input reads), the depth
check (at most 32), the leaf copied into `MERKLE.state`, then the loop (`mc_loop`) or, for depth 0, the end
(`mc_exit`). `merkle_step` is any implementation of its contract. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

/-- Words 15 … 23: the root into `s9, s8, s7, s6, s4, s5, s3, s2`, the depth into `s11`. -/
def mcRootReads (root : Vector Word 8) (d : Word) : List (Reg × Word) :=
  [(25#5, root[0]), (24#5, root[1]), (23#5, root[2]), (22#5, root[3]), (20#5, root[4]), (21#5, root[5]),
    (19#5, root[6]), (18#5, root[7]), (27#5, d)]

theorem pathInput_eq (root : Vector Word 8) (path : List MerkleStep) :
    pathInput root path = root.toList ++ BitVec.ofNat 32 path.length :: pathWords path := by
  simp only [pathInput, pathWords]

theorem merkle_check_run (A : Word) (codeS : List Word) (calleesS : List (Word × List Word)) (FS al len : Nat)
    (hS : ImplementsAtW (A + 0x1bc#32) codeS calleesS FS (merklePre al len) len merklePost)
    (s0 : State) (F : Nat) (root : Vector Word 8) (path : List MerkleStep) (rest : List Word)
    (hpc : s0.pc = A) (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * 111 + 0x21c + 24 ≤ ROM_END)
    (hSr : (A + 0x1bc#32).toNat + 4 * codeS.length ≤ ROM_END)
    (hcalr : ∀ c ∈ calleesS, c.1.toNat + 4 * c.2.length ≤ ROM_END)
    (hcode : CodeAt s0 A Code.merkle_check) (herr : CodeAt s0 (A + 0x3d4#32) Code.finish_error)
    (hcS : CodeAt s0 (A + 0x1bc#32) codeS) (hcal : ∀ c ∈ calleesS, CodeAt s0 c.1 c.2)
    (hMal : MERKLE.toNat % al = 0) (hlen : len ≤ 256) (hlen32 : 32 ≤ len) (hF : 96 + FS ≤ F) (hF2 : 112 ≤ F)
    (hsp0 : ROM_END + F ≤ (s0.getReg 2#5).toNat) (hsp0' : (s0.getReg 2#5).toNat ≤ 0x1400000)
    (hsp16 : (s0.getReg 2#5).toNat % 16 = 0) (hra : (s0.getReg 1#5).toNat % 4 = 0)
    (hlf : (s0.getReg 10#5).toNat % 4 = 0) (hlf1 : (s0.getReg 2#5).toNat ≤ (s0.getReg 10#5).toNat)
    (hlf2 : (s0.getReg 10#5).toNat + 32 ≤ MERKLE.toNat ∨ MERKLE.toNat + len ≤ (s0.getReg 10#5).toNat)
    (hlf3 : (s0.getReg 10#5).toNat + 32 ≤ RAM_END)
    (hin : s0.input = pathInput root path ++ rest) (hd : path.length ≤ 32) :
    ∃ m T, run m s0 = some T ∧
      McFinal s0 F len (merkleRoot (readWords s0.mem (s0.getReg 10#5) 8) path) root rest T := by
  have hL : Code.merkle_check.length = 111 := by decide +kernel
  have hromL : A.toNat + 4 * Code.merkle_check.length ≤ ROM_END := by
    rw [hL]; simp only [ROM_END] at hrom ⊢; omega
  have hsp0r := hsp0
  simp only [ROM_END] at hsp0r
  simp only [RAM_END] at hlf3
  have hMn : MERKLE.toNat = 0x1401100 := rfl
  -- the prologue, words 0 … 14: the frame, the 13 saved registers below `sp₀`
  obtain ⟨S1, hrun1, hpc1, hin1, hrel1, hrom1, hout1, hfr1⟩ := block_at Code.merkle_check 0 15 MPro.instrs MPro.σ s0 A
    [⟨2, -52, 0, 4⟩] [] MPro.dec MPro.run (by rw [hL]; omega) (by rw [hpc]; simp) hal hromL hcode (by sym_side)
    (by simp) (by decide +kernel)
  have mS1 : ∀ a : Word, a.toNat + 52 < (s0.getReg 2#5).toNat ∨ (s0.getReg 2#5).toNat ≤ a.toNat →
      S1.mem a = s0.mem a := fun a ha =>
    out_frame hfr1 ⟨2, -52, 0, 1⟩ (by decide +kernel) (by decide) (by sym_side) a
      (by simp only [Region.Outside]; omega)
  have sv : ∀ (k : Word) (r : Nat), r < 32 → outOK MPro.σ [⟨2, -52, 0, 4⟩] [] 2 k = true →
      outNode MPro.σ 2 k = r → read S1.mem (s0.getReg 2#5 + k) 4 = s0.getReg (BitVec.ofNat 5 r) :=
    fun k r hr hok hn => by rw [hout1 2 k (by decide) hok, hn]; exact val_init MPro.instrs MPro.σ MPro.run s0 r hr
  have s1sp : S1.getReg 2#5 = s0.getReg 2#5 + 4294967200#32 :=
    Rel.reg_addr MPro.instrs MPro.run hrel1 2#5 2 4294967200#32 (by decide) (by decide +kernel) (by decide +kernel)
  -- the root and the depth, words 15 … 23
  have hinS : S1.input = (mcRootReads root (BitVec.ofNat 32 path.length)).map (·.2) ++ (pathWords path ++ rest) := by
    rw [hin1, hin, pathInput_eq, vec8_toList]; rfl
  have hcode1 : CodeAt S1 A Code.merkle_check := codeAt_of_rom hcode hromL hrom1
  have hR := run_reads (mcRootReads root (BitVec.ofNat 32 path.length)) S1 _ hinS (by rw [hpc1]; bv_omega)
    (by rw [hpc1]; simp only [mcRootReads, List.length_cons, List.length_nil, ROM_END] at hrom ⊢; bv_omega)
    (fun i hi => by
      simp only [mcRootReads, List.length_cons, List.length_nil] at hi
      rw [hpc1, show A + BitVec.ofNat 32 (4 * (0 + 15)) + BitVec.ofNat 32 (4 * i) =
        A + BitVec.ofNat 32 (4 * (15 + i)) by bv_omega, hcode1 (15 + i) (by rw [hL]; omega), ← getElem!_pos]
      interval_cases i <;> simp only [mcRootReads, List.getElem_cons_succ, List.getElem_cons_zero] <;> decide +kernel)
  apply run_of_run s0 _ _ _ (run_trans hrun1 hR)
  obtain ⟨X, hX⟩ : ∃ X, X = (readsTo S1 (mcRootReads root (BitVec.ofNat 32 path.length))).withInput
      (pathWords path ++ rest) := ⟨_, rfl⟩
  rw [← hX]
  have hXpc : X.pc = A + BitVec.ofNat 32 (4 * 24) := by
    rw [hX, withInput_pc, readsTo_pc, hpc1]; simp only [mcRootReads, List.length_cons, List.length_nil]; bv_omega
  have hXm : X.mem = S1.mem := by rw [hX, withInput_mem, readsTo_mem]
  have hXin : X.input = pathWords path ++ rest := by rw [hX, withInput_input]
  have hXr : ∀ r v, (r, v) ∈ mcRootReads root (BitVec.ofNat 32 path.length) → r ≠ 0 → X.getReg r = v :=
    fun r v h h0 => by
      rw [hX, withInput_getReg]
      exact readsTo_getReg _ S1 r v (by simp only [mcRootReads, List.map_cons, List.map_nil]; decide) h0 h
  have hXo : ∀ r, (∀ p ∈ mcRootReads root (BitVec.ofNat 32 path.length), p.1 ≠ r) → X.getReg r = S1.getReg r :=
    fun r h => by rw [hX, withInput_getReg]; exact readsTo_getReg_other _ S1 r h
  have hcodeX : CodeAt X A Code.merkle_check := fun i h => by rw [hXm]; exact hcode1 i h
  have hX27 : X.getReg 27#5 = BitVec.ofNat 32 path.length := hXr _ _ (by simp [mcRootReads]) (by decide)
  -- the depth check, words 24, 25 (at most 32: no branch to the error)
  obtain ⟨S2, hrun2, hpc2, hin2, hrel2, hrom2, -, -⟩ := block_at Code.merkle_check 24 1 MLim.instrs MLim.σ X A
    [] [] MLim.dec MLim.run (by rw [hL]; omega) hXpc hal hromL hcodeX (by simp) (by simp) (by decide +kernel)
  have s2r : ∀ r : Reg, (MLim.σ.reg r).val = r.toNat → S2.getReg r = X.getReg r := fun r h =>
    Rel.reg_same MLim.instrs MLim.run hrel2 r h
  have hbf := run_branch_f hcodeX hal hromL hrom2 25 0x15b5ea63#32 (by decide +kernel) hpc2 .ltu 11#5 27#5
    0x154#32 (by decide +kernel) (by
      rw [Rel.reg_cst hrel2 11#5 32#32 (by decide +kernel), s2r _ (by decide +kernel), hX27]
      simp only [Cond.holds, BitVec.ult, BitVec.toNat_ofNat]; simp; omega)
  apply run_of_run X _ _ _ (run_trans hrun2 hbf)
  have hcode2 : CodeAt S2.nextInstr A Code.merkle_check := codeAt_of_rom hcodeX hromL (fun b hb => hrom2 b hb)
  -- the leaf's words into `a0 … a7`, `s10 = MERKLE - 0x100`, words 26 … 34
  have hlf' : (S2.nextInstr.getReg 10#5) = s0.getReg 10#5 := by
    rw [next_r, s2r _ (by decide +kernel), hXo _ (by simp [mcRootReads]),
      Rel.reg_same MPro.instrs MPro.run hrel1 10#5 (by decide +kernel)]
  have s2sp : S2.nextInstr.getReg 2#5 = s0.getReg 2#5 + 4294967200#32 := by
    rw [next_r, s2r _ (by decide +kernel), hXo _ (by simp [mcRootReads]), s1sp]
  obtain ⟨S3, hrun3, hpc3, hin3, hrel3, hrom3, -, -⟩ := block_at Code.merkle_check 26 9 MLoad.instrs MLoad.σ
    S2.nextInstr A [⟨10, 0, 32, 4⟩] [] MLoad.dec MLoad.run (by rw [hL]; omega) (by rw [next_pc, hpc2]; bv_omega) hal
    hromL hcode2 (by have := congrArg BitVec.toNat hlf'; sym_side) (by simp) (by decide +kernel)
  have s3r : ∀ r : Reg, (MLoad.σ.reg r).val = r.toNat → S3.getReg r = S2.nextInstr.getReg r := fun r h =>
    Rel.reg_same MLoad.instrs MLoad.run hrel3 r h
  have s3m : S3.mem = S1.mem := by
    rw [Rel.mem_nil hrel3 (by decide +kernel), next_mem, Rel.mem_nil hrel2 (by decide +kernel), hXm]
  have s3_26 : S3.getReg 26#5 = 0x1401000#32 := Rel.reg_cst hrel3 26#5 _ (by decide +kernel)
  have s3_26n : (S3.getReg 26#5).toNat = 0x1401000 := by rw [s3_26]; rfl
  have hcode3 : CodeAt S3 A Code.merkle_check := codeAt_of_rom hcode2 hromL (fun b hb => hrom3 b hb)
  -- the leaf into `MERKLE.state`, words 35 … 42
  obtain ⟨S4, hrun4, hpc4, hin4, hrel4, hrom4, hout4, hfr4⟩ := block_at Code.merkle_check 35 8 MStore.instrs
    MStore.σ S3 A [⟨26, 256, 288, 4⟩] [] MStore.dec MStore.run (by rw [hL]; omega) (by rw [hpc3]) hal
    hromL hcode3 (by sym_side) (by simp) (by decide +kernel)
  apply run_of_run S2.nextInstr _ _ _ (run_trans hrun3 hrun4)
  have mS4 : ∀ a : Word, a.toNat < MERKLE.toNat ∨ MERKLE.toNat + 32 ≤ a.toNat → S4.mem a = S1.mem a := fun a ha => by
    rw [← s3m]
    exact out_frame hfr4 ⟨26, 256, 288, 1⟩ (by decide +kernel) (by decide) (by sym_side) a
      (by simp only [Region.Outside]; rw [hMn] at ha; omega)
  -- the leaf, read back from `MERKLE.state`
  have lw : ∀ (k : Word) (r : Nat) (k' : Word), r < 32 → outOK MStore.σ [⟨26, 256, 288, 4⟩] [] 26 k = true →
      outNode MStore.σ 26 k = r → (MLoad.σ.reg (BitVec.ofNat 5 r)).val < MLoad.σ.pool.len →
      nodeAt MLoad.σ.pool (MLoad.σ.reg (BitVec.ofNat 5 r)).val = .load 4 true 10 k' → k'.toNat ≤ 28 →
      read S4.mem (S3.getReg 26#5 + k) 4 = read s0.mem (s0.getReg 10#5 + k') 4 := fun k r k' hr hok hn hi hl hk => by
    rw [hout4 26 k (by decide) hok, hn, val_init MStore.instrs MStore.σ MStore.run S3 r hr,
      Rel.reg_load MLoad.instrs MLoad.run hrel3 _ 10 k' (by decide) hi hl, hlf', next_mem,
      Rel.mem_nil hrel2 (by decide +kernel), hXm]
    exact read_congr _ _ _ _ (fun j hj => mS1 _ (by right; rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega))
  have hleaf : readWords S4.mem MERKLE 8 = readWords s0.mem (s0.getReg 10#5) 8 := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    rw [show MERKLE = S3.getReg 26#5 + 256#32 by rw [s3_26]; rfl, BitVec.add_assoc]
    interval_cases i
    · exact lw _ 10 _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    · exact lw _ 15 _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    · exact lw _ 16 _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    · exact lw _ 17 _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    · exact lw _ 14 _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    · exact lw _ 11 _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    · exact lw _ 12 _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    · exact lw _ 13 _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
  -- the frame at word 43
  have keep : ∀ r : Reg, (MStore.σ.reg r).val = r.toNat → (MLoad.σ.reg r).val = r.toNat →
      (MLim.σ.reg r).val = r.toNat → S4.getReg r = X.getReg r := fun r h4 h3 h2 => by
    rw [Rel.reg_same MStore.instrs MStore.run hrel4 r h4, s3r r h3, next_r, s2r r h2]
  have kr : ∀ r v, (r, v) ∈ mcRootReads root (BitVec.ofNat 32 path.length) → r ≠ 0 →
      (MStore.σ.reg r).val = r.toNat → (MLoad.σ.reg r).val = r.toNat → (MLim.σ.reg r).val = r.toNat →
      S4.getReg r = v := fun r v hm h0 h4 h3 h2 => (keep r h4 h3 h2).trans (hXr r v hm h0)
  have vS : ∀ (c r : Nat), 4 ≤ c → c ≤ 52 → r < 32 →
      outOK MPro.σ [⟨2, -52, 0, 4⟩] [] 2 (BitVec.ofNat 32 (4294967296 - c)) = true →
      outNode MPro.σ 2 (BitVec.ofNat 32 (4294967296 - c)) = r →
      read S4.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4 = s0.getReg (BitVec.ofNat 5 r) :=
    fun c r h1 h2 hr hok hn => by
      have ea := frame_addr (s0.getReg 2#5) c (by omega) (by omega)
      rw [read_congr _ S1.mem _ _ (fun j hj => mS4 _ (by left; rw [BitVec.toNat_add, ea, hMn]; simp; omega)),
        sv _ r hr hok hn]
  have hrom4' : ∀ b : Word, b.toNat < ROM_END → S4.mem b = s0.mem b := fun b hb => by
    rw [hrom4 b hb, hrom3 b hb, next_mem, hrom2 b hb, hXm, hrom1 b hb]
  have frC : MFrame s0 F len root S4 :=
    ⟨by rw [keep _ (by decide +kernel) (by decide +kernel) (by decide +kernel), hXo _ (by simp [mcRootReads]), s1sp],
      by rw [Rel.reg_same MStore.instrs MStore.run hrel4 _ (by decide +kernel), s3_26],
      kr _ _ (by simp [mcRootReads]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      kr _ _ (by simp [mcRootReads]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      kr _ _ (by simp [mcRootReads]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      kr _ _ (by simp [mcRootReads]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      kr _ _ (by simp [mcRootReads]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      kr _ _ (by simp [mcRootReads]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      kr _ _ (by simp [mcRootReads]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      kr _ _ (by simp [mcRootReads]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      vS 4 1 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 8 8 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 12 9 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 16 18 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 20 19 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 24 20 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 28 21 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 32 22 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 36 23 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 40 24 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 44 25 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 48 26 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      vS 52 27 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
      fun a ha hb => by
        rw [mS4 a (by rw [hMn] at hb ⊢; omega)]; exact mS1 a (by omega),
      hrom4'⟩
  have s4_27 : S4.getReg 27#5 = BitVec.ofNat 32 path.length := by
    rw [keep _ (by decide +kernel) (by decide +kernel) (by decide +kernel), hX27]
  have s4in : S4.input = pathWords path ++ rest := by rw [hin4, hin3, nextInstr_input, hin2, hXin]
  have hcode4 : CodeAt S4 A Code.merkle_check := codeAt_of_rom hcode hromL hrom4'
  have hlE : Code.finish_error.length = 6 := by decide +kernel
  by_cases hp0 : path.length = 0
  · -- depth 0: to the end (word 68)
    have hpath : path = [] := List.eq_nil_of_length_eq_zero hp0
    have hbt := run_branch_t hcode4 hal hromL (fun _ _ => rfl) 43 0x060d8263#32 (by decide +kernel) hpc4 .eq 27#5
      0#5 0x64#32 (by decide +kernel) (by rw [s4_27, r_zero5, hp0]; decide) 68 (by decide)
    have heE : CodeAt (S4.setPC (A + BitVec.ofNat 32 (4 * 68))) (A + 0x3d4#32) Code.finish_error :=
      codeAt_of_rom herr (by rw [hlE]; simp only [ROM_END] at hrom ⊢; bv_omega) hrom4'
    obtain ⟨m, T, hT, hfin⟩ := mc_exit s0 (S4.setPC (A + BitVec.ofNat 32 (4 * 68))) A F len root rest hal hrom
      (codeAt_of_rom hcode hromL hrom4') heE
      (by rw [jump_pc]) (frC.of_eq (jump_mem _ _) (fun r _ => jump_r _ _ r))
      (by rw [show (S4.setPC (A + BitVec.ofNat 32 (4 * 68))).input = S4.input from rfl, s4in, hpath]; rfl)
      hF2 hsp0 hsp0' hsp16 hra
    refine ⟨1 + m, T, run_trans hbt hT, ?_⟩
    rw [jump_mem, hleaf] at hfin
    rw [hpath]; exact hfin
  · -- the loop, from word 46 with `s1 = MERKLE`
    have hz : BitVec.ofNat 32 path.length ≠ 0#32 := by
      intro h; apply hp0; have := congrArg BitVec.toNat h; simp at this; omega
    have hbf := run_branch_f hcode4 hal hromL (fun _ _ => rfl) 43 0x060d8263#32 (by decide +kernel) hpc4 .eq 27#5
      0#5 0x64#32 (by decide +kernel) (by rw [s4_27, r_zero5]; simp [Cond.holds, hz])
    obtain ⟨S5, hrun5, hpc5, hin5, hrel5, hrom5, -, -⟩ := block_at Code.merkle_check 44 2 MS1.instrs MS1.σ
      S4.nextInstr A [] [] MS1.dec MS1.run (by rw [hL]; omega) (by rw [next_pc, hpc4]; bv_omega) hal hromL
      (codeAt_of_rom hcode4 hromL (fun _ _ => rfl)) (by simp) (by simp) (by decide +kernel)
    have m5 : S5.mem = S4.mem := by rw [Rel.mem_nil hrel5 (by decide +kernel), next_mem]
    have fr5 : MFrame s0 F len root S5 := frC.of_eq m5 (fun r hr => by
      rcases hr with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
        exact (Rel.reg_same MS1.instrs MS1.run hrel5 _ (by decide +kernel)).trans (next_r _ _))
    obtain ⟨m1, E, hE, pcE, frE, inE, nE⟩ := mc_loop A codeS calleesS FS al len hS s0 F _ root path rest hal hrom
      hSr hcalr hcode herr hcS hcal hMal hlen hF hF2 hsp0 hsp0' hsp16 hra hd path.length 0 S5 (by omega) (by omega)
      (by rw [hpc5]) fr5 (Rel.reg_cst hrel5 9#5 _ (by decide +kernel))
      (by rw [Rel.reg_same MS1.instrs MS1.run hrel5 _ (by decide +kernel), next_r, s4_27])
      (by rw [m5, hleaf]; rfl) (by rw [hin5, nextInstr_input, s4in]; rfl)
    have hcE : CodeAt E A Code.merkle_check := codeAt_of_rom hcode hromL frE.rom
    have heE : CodeAt E (A + 0x3d4#32) Code.finish_error := codeAt_of_rom herr (by
      rw [hlE]; simp only [ROM_END] at hrom ⊢; bv_omega) frE.rom
    obtain ⟨m2, T, hT, hfin⟩ := mc_exit s0 E A F len root rest hal hrom hcE heE pcE frE inE hF2 hsp0 hsp0' hsp16 hra
    exact ⟨1 + 2 + (m1 + m2), T, run_trans (run_trans hbf hrun5) (run_trans hE hT), nE ▸ hfin⟩
end RV
