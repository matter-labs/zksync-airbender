import Slop.RV.Merkle.Loop

/-! `merkle_check(leaf)`, the whole function: the prologue, the root and the depth (9 input reads), the depth
check (at most 32), the leaf copied into `MERKLE.state`, then the loop (`mc_loop`) or, for depth 0, the end
(`mc_exit`). `merkle_step` is any implementation of its contract. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Words 15 … 23: the root into `s9, s8, s7, s6, s4, s5, s3, s2`, the depth into `s11`. -/
def mcRootReads (root : Vector Word 8) (d : Word) : List (Reg × Word) :=
  [(25#5, root[0]), (24#5, root[1]), (23#5, root[2]), (22#5, root[3]), (20#5, root[4]), (21#5, root[5]),
    (19#5, root[6]), (18#5, root[7]), (27#5, d)]

/-- A word stored above the stack (from `0x1400000` on) does not change a word read below it. -/
theorem read_write_hi {m : Word → BitVec 8} {b : Word} (hb : b.toNat + 4 ≤ 0x1400000) (a v : Word)
    (ha : 0x1400000 ≤ a.toNat) (ha2 : a.toNat + 4 ≤ 2 ^ 32) : read (write m a v 4) b 4 = read m b 4 :=
  read_write_disjoint m a v b 4 4 (Or.inr (by omega)) ha2 (by omega)

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
  have hrom' := hrom
  have hsp0r := hsp0
  simp only [ROM_END, RAM_END] at hrom' hsp0r hlf3
  rv_code_facts hcode Code.merkle_check
  rv_steps 15 with hpc
  rv_cut with hin
  have srom : ∀ b : Word, b.toNat < ROM_END → S.mem b = s0.mem b := fun b hb => by
    simp only [ROM_END] at hb
    rw [cut_mem]
    repeat rw [write_outside (h := Or.inl (by bv_omega)) (ha := by bv_omega)]
  have hcodeS : CodeAt S A Code.merkle_check := codeAt_of_rom hcode (by
    rw [show Code.merkle_check.length = 111 from rfl]; simp only [ROM_END]; omega) srom
  -- the root and the depth
  have hinS : S.input = (mcRootReads root (BitVec.ofNat 32 path.length)).map (·.2) ++ (pathWords path ++ rest) := by
    rw [cut_input, pathInput_eq, vec8_toList]; rfl
  have hR := run_reads (mcRootReads root (BitVec.ofNat 32 path.length)) S _ hinS (by rw [cut_pc, hpc]; bv_omega)
    (by rw [cut_pc, hpc]; simp only [mcRootReads, List.length_cons, List.length_nil, ROM_END]; bv_omega)
    (fun i hi => by
      simp only [mcRootReads, List.length_cons, List.length_nil] at hi
      rw [cut_pc, hpc, show A + 60#32 + BitVec.ofNat 32 (4 * i) = A + BitVec.ofNat 32 (4 * (15 + i)) by bv_omega,
        hcodeS (15 + i) (by rw [show Code.merkle_check.length = 111 from rfl]; omega), ← getElem!_pos]
      interval_cases i <;> simp only [mcRootReads, List.getElem_cons_succ, List.getElem_cons_zero] <;> decide +kernel)
  rw [readsTo_withInput_comm] at hR
  apply run_of_run S _ _ _ hR
  obtain ⟨L', hL'⟩ : ∃ L', L' = S.withInput (pathWords path ++ rest) := ⟨_, rfl⟩
  rw [← hL']
  have pc' : L'.pc = A + 60#32 := by rw [hL', withInput_pc, cut_pc, hpc]
  have m' : L'.mem = S.mem := by rw [hL', withInput_mem]
  have g' : ∀ r, L'.getReg r = S.getReg r := fun r => by rw [hL', withInput_getReg]
  have in' : L'.input = pathWords path ++ rest := by rw [hL', withInput_input]
  have hcodeL' : CodeAt L' A Code.merkle_check := fun i h => by rw [m']; exact hcodeS i h
  have Lsp : L'.getReg 2#5 = s0.getReg 2#5 + 4294967200#32 := (g' _).trans cut_r2
  have Lm := m'.trans cut_mem
  unfold mcRootReads
  simp only [readsTo.eq_2, readsTo.eq_1]
  rv_code_facts hcodeL' Code.merkle_check
  have hult : (32#32).ult (BitVec.ofNat 32 path.length) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat]; simp; omega
  rv_steps 1 with pc', g'
  apply run_of_step
  rv_step_simp with pc', g'
  rv_steps 17 with pc', g'
  rv_cut with in'
  -- the frame: what the prologue saved, the root, memory outside the frame and `MERKLE`
  have rdC : ∀ (b : Word), b.toNat + 4 ≤ (s0.getReg 2#5).toNat → (s0.getReg 2#5).toNat - 52 ≤ b.toNat →
      read S.mem b 4 = read (write (write (write (write (write (write (write (write (write (write (write (write
        (write s0.mem (s0.getReg 2#5 + 4294967292#32) (s0.getReg 1#5) 4) (s0.getReg 2#5 + 4294967288#32)
        (s0.getReg 8#5) 4) (s0.getReg 2#5 + 4294967284#32) (s0.getReg 9#5) 4) (s0.getReg 2#5 + 4294967280#32)
        (s0.getReg 18#5) 4) (s0.getReg 2#5 + 4294967276#32) (s0.getReg 19#5) 4) (s0.getReg 2#5 + 4294967272#32)
        (s0.getReg 20#5) 4) (s0.getReg 2#5 + 4294967268#32) (s0.getReg 21#5) 4) (s0.getReg 2#5 + 4294967264#32)
        (s0.getReg 22#5) 4) (s0.getReg 2#5 + 4294967260#32) (s0.getReg 23#5) 4) (s0.getReg 2#5 + 4294967256#32)
        (s0.getReg 24#5) 4) (s0.getReg 2#5 + 4294967252#32) (s0.getReg 25#5) 4) (s0.getReg 2#5 + 4294967248#32)
        (s0.getReg 26#5) 4) (s0.getReg 2#5 + 4294967244#32) (s0.getReg 27#5) 4) b 4 := fun b h1 h2' => by
    have hb : b.toNat + 4 ≤ 20971520 := by omega
    rw [cut_mem]
    simp (disch := decide) only [read_write_hi hb]
    rw [Lm]
  have sv : ∀ (k : Word) (v : Word), (s0.getReg 2#5 + k).toNat + 4 ≤ (s0.getReg 2#5).toNat →
      (s0.getReg 2#5).toNat - 52 ≤ (s0.getReg 2#5 + k).toNat →
      read (write (write (write (write (write (write (write (write (write (write (write (write
        (write s0.mem (s0.getReg 2#5 + 4294967292#32) (s0.getReg 1#5) 4) (s0.getReg 2#5 + 4294967288#32)
        (s0.getReg 8#5) 4) (s0.getReg 2#5 + 4294967284#32) (s0.getReg 9#5) 4) (s0.getReg 2#5 + 4294967280#32)
        (s0.getReg 18#5) 4) (s0.getReg 2#5 + 4294967276#32) (s0.getReg 19#5) 4) (s0.getReg 2#5 + 4294967272#32)
        (s0.getReg 20#5) 4) (s0.getReg 2#5 + 4294967268#32) (s0.getReg 21#5) 4) (s0.getReg 2#5 + 4294967264#32)
        (s0.getReg 22#5) 4) (s0.getReg 2#5 + 4294967260#32) (s0.getReg 23#5) 4) (s0.getReg 2#5 + 4294967256#32)
        (s0.getReg 24#5) 4) (s0.getReg 2#5 + 4294967252#32) (s0.getReg 25#5) 4) (s0.getReg 2#5 + 4294967248#32)
        (s0.getReg 26#5) 4) (s0.getReg 2#5 + 4294967244#32) (s0.getReg 27#5) 4) (s0.getReg 2#5 + k) 4 = v →
      read S.mem (s0.getReg 2#5 + k) 4 = v := fun k v h1 h2' h => (rdC _ h1 h2').trans h
  have frC : MFrame s0 F len root S := by
    refine ⟨by rw [cut_r2, Lsp], cut_r26, cut_r25, cut_r24, cut_r23, cut_r22, cut_r20, cut_r21, cut_r19, cut_r18,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_right 2
    all_goals first
      | (apply sv _ _ (by bv_omega) (by bv_omega)
         simp (disch := decide) only [read_write_off, read_write_same4])
      | skip
    · intro a ha hb
      rw [cut_mem]
      repeat rw [write_outside (h := by bv_omega) (ha := by bv_omega)]
      rw [Lm]
      repeat rw [write_outside (h := by bv_omega) (ha := by bv_omega)]
    · intro b hb
      simp only [ROM_END] at hb
      rw [cut_mem]
      repeat rw [write_outside (h := by bv_omega) (ha := by bv_omega)]
      rw [Lm]
      repeat rw [write_outside (h := by bv_omega) (ha := by bv_omega)]
  -- the leaf, copied into `MERKLE.state`
  have hleaf : readWords S.mem MERKLE 8 = readWords s0.mem (s0.getReg 10#5) 8 := by
    rw [cut_mem, readWords_merkle]
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    rw [Lm]
    interval_cases i <;> simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] <;>
      exact read_above_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by bv_omega) (by omega) (by bv_omega)
  have hlE : Code.finish_error.length = 6 := by decide +kernel
  have cpc := cut_pc
  have c9 := cut_r9
  have cin := cut_input
  have cmem := cut_mem
  have c2 := cut_r2; have c18 := cut_r18; have c19 := cut_r19; have c20 := cut_r20; have c21 := cut_r21
  have c22 := cut_r22; have c23 := cut_r23; have c24 := cut_r24; have c25 := cut_r25; have c26 := cut_r26
  by_cases hp0 : path.length = 0
  · have hz : BitVec.ofNat 32 path.length = 0#32 := by rw [hp0]
    apply run_of_step
    rv_step_simp with cut_r27, hz, pc'
    rw [exec_branch_t _ _ _ _ _ (by simp only [Cond.holds, cut_r27, hz, r_zero5]; decide)
      (by rw [cut_pc, pc']; bv_omega), Option.elim_some]
    rv_cut
    have fr' : MFrame s0 F len root S := frC.of_eq (by rw [cut_mem, cmem]) (fun r hr => by
      rcases hr with h|h|h|h|h|h|h|h|h|h <;> subst h
      · rw [cut_r2, c2]
      · rw [cut_r26, c26]
      · rw [cut_r25, c25]
      · rw [cut_r24, c24]
      · rw [cut_r23, c23]
      · rw [cut_r22, c22]
      · rw [cut_r21, c21]
      · rw [cut_r20, c20]
      · rw [cut_r19, c19]
      · rw [cut_r18, c18])
    have hcE : CodeAt S A Code.merkle_check := codeAt_of_rom hcode (by
      rw [show Code.merkle_check.length = 111 from rfl]; simp only [ROM_END]; omega) fr'.rom
    have heE : CodeAt S (A + 0x3d4#32) Code.finish_error := codeAt_of_rom herr (by
      rw [hlE]; simp only [ROM_END]; bv_omega) fr'.rom
    have hpath : path = [] := List.eq_nil_of_length_eq_zero hp0
    obtain ⟨m, T, hT, hfin⟩ := mc_exit s0 S A F len root rest hal hrom hcE heE
      (by rw [cut_pc, pc']; bv_omega) fr' (by rw [cut_input, hpath]; rfl) hF2 hsp0 hsp0' hsp16 hra
    refine ⟨m, T, hT, ?_⟩
    rw [cut_mem, ← cmem, hleaf] at hfin
    rw [hpath]; exact hfin
  · have hz : BitVec.ofNat 32 path.length ≠ 0#32 := by
      intro h; apply hp0; have := congrArg BitVec.toNat h; simp at this; omega
    rv_steps 3 with cut_r27, hz, pc'
    rv_cut
    have fr' : MFrame s0 F len root S := frC.of_eq (by rw [cut_mem, cmem]) (fun r hr => by
      rcases hr with h|h|h|h|h|h|h|h|h|h <;> subst h
      · rw [cut_r2, c2]
      · rw [cut_r26, c26]
      · rw [cut_r25, c25]
      · rw [cut_r24, c24]
      · rw [cut_r23, c23]
      · rw [cut_r22, c22]
      · rw [cut_r21, c21]
      · rw [cut_r20, c20]
      · rw [cut_r19, c19]
      · rw [cut_r18, c18])
    exact mc_loop A codeS calleesS FS al len hS s0 F _ root path rest hal hrom hSr hcalr hcode herr hcS hcal hMal hlen
      hF hF2 hsp0 hsp0' hsp16 hra hd path.length 0 S (by omega) (by omega) (by rw [cut_pc, pc']; bv_omega) fr'
      (by rw [cut_r9]) (by rw [cut_r27]) (by rw [cut_mem, ← cmem, hleaf]; rfl) (by rw [cut_input]; rfl)

end RV
