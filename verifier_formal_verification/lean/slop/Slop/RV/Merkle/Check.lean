import Slop.RV.Merkle.Loop
import Slop.RV.Frame

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
  -- the frame: the prologue's stores (below `sp`) and the leaf's (below `MERKLE + 32`) as lists
  have hsp4 : (s0.getReg 2#5).toNat % 4 = 0 := by omega
  obtain ⟨l13, hl13d⟩ : ∃ l : List (Nat × Word), l = [(4, s0.getReg 1#5), (8, s0.getReg 8#5),
      (12, s0.getReg 9#5), (16, s0.getReg 18#5), (20, s0.getReg 19#5), (24, s0.getReg 20#5), (28, s0.getReg 21#5),
      (32, s0.getReg 22#5), (36, s0.getReg 23#5), (40, s0.getReg 24#5), (44, s0.getReg 25#5), (48, s0.getReg 26#5),
      (52, s0.getReg 27#5)] := ⟨_, rfl⟩
  obtain ⟨l8, hl8d⟩ : ∃ l : List (Nat × Word), l = [(4, read L'.mem (s0.getReg 10#5 + 28#32) 4),
      (8, read L'.mem (s0.getReg 10#5 + 24#32) 4), (12, read L'.mem (s0.getReg 10#5 + 20#32) 4),
      (16, read L'.mem (s0.getReg 10#5 + 16#32) 4), (20, read L'.mem (s0.getReg 10#5 + 12#32) 4),
      (24, read L'.mem (s0.getReg 10#5 + 8#32) 4), (28, read L'.mem (s0.getReg 10#5 + 4#32) 4),
      (32, read L'.mem (s0.getReg 10#5) 4)] := ⟨_, rfl⟩
  have hPro : L'.mem = frameWrites s0.mem (s0.getReg 2#5) l13 := by rw [Lm, hl13d]; rfl
  have hMk : S.mem = frameWrites L'.mem 0x1401120#32 l8 := by rw [cut_mem, hl8d]; rfl
  have hl13 : ∀ p ∈ l13, 4 ≤ p.1 ∧ p.1 ≤ 52 ∧ p.1 % 4 = 0 := by
    rw [hl13d]; intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  have hl8 : ∀ p ∈ l8, 4 ≤ p.1 ∧ p.1 ≤ 32 ∧ p.1 % 4 = 0 := by
    rw [hl8d]; intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  have hl13s : ∀ p ∈ l13, 4 ≤ p.1 ∧ p.1 ≤ (s0.getReg 2#5).toNat ∧ p.1 % 4 = 0 := fun p hp =>
    ⟨(hl13 p hp).1, by have := (hl13 p hp).2.1; omega, (hl13 p hp).2.2⟩
  have hl8s : ∀ p ∈ l8, 4 ≤ p.1 ∧ p.1 ≤ (0x1401120#32 : Word).toNat ∧ p.1 % 4 = 0 := fun p hp =>
    ⟨(hl8 p hp).1, by have := (hl8 p hp).2.1; simp; omega, (hl8 p hp).2.2⟩
  have hl13D : ∀ p ∈ l13, 4 ≤ p.1 ∧ p.1 ≤ 52 := fun p hp => ⟨(hl13 p hp).1, (hl13 p hp).2.1⟩
  have hl8D : ∀ p ∈ l8, 4 ≤ p.1 ∧ p.1 ≤ 32 := fun p hp => ⟨(hl8 p hp).1, (hl8 p hp).2.1⟩
  -- a saved word, read in the frame
  have vf : ∀ c, 4 ≤ c → c ≤ 52 → c % 4 = 0 →
      read S.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4 =
        frameLookup c (read s0.mem (s0.getReg 2#5 + BitVec.ofNat 32 (4294967296 - c)) 4) l13 := by
    intro c h1 h2 h3
    have ea := frame_addr (s0.getReg 2#5) c (by omega) (by omega)
    rw [hMk, read_frameWrites_out _ 4 32 (by decide) (by decide) _ _ _ hl8D (Or.inl (by rw [ea]; simp; omega)) (by rw [ea]; omega),
      hPro]
    exact read_frameWrites _ hsp4 _ _ c hl13s h1 (by omega) h3
  have frC : MFrame s0 F len root S := by
    refine ⟨by rw [cut_r2, Lsp], cut_r26, cut_r25, cut_r24, cut_r23, cut_r22, cut_r20, cut_r21, cut_r19, cut_r18,
      (vf 4 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 8 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 12 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 16 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 20 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 24 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 28 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 32 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 36 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 40 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 44 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 48 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]),
      (vf 52 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl13d]), ?_, ?_⟩
    · intro a ha hb
      rw [hMk, frameWrites_outside _ 4 32 (by decide) (by decide) _ _ _ hl8D (by have : MERKLE.toNat = 0x1401100 := rfl; simp; omega), hPro,
        frameWrites_outside _ 4 52 (by decide) (by omega) _ _ _ hl13D (by omega)]
    · intro b hb
      simp only [ROM_END] at hb
      rw [hMk, frameWrites_outside _ 4 32 (by decide) (by decide) _ _ _ hl8D (by simp; omega), hPro,
        frameWrites_outside _ 4 52 (by decide) (by omega) _ _ _ hl13D (by omega)]
  -- the leaf, copied into `MERKLE.state`
  have hleaf : readWords S.mem MERKLE 8 = readWords s0.mem (s0.getReg 10#5) 8 := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    have ab : ∀ k : Word, k.toNat ≤ 28 → read L'.mem (s0.getReg 10#5 + k) 4 = read s0.mem (s0.getReg 10#5 + k) 4 :=
      fun k hk => by
        rw [hPro]
        apply read_frameWrites_out _ 4 52 (by decide) (by omega) _ _ _ hl13D
        · right; rw [BitVec.toNat_add]; simp; omega
        · rw [BitVec.toNat_add]; simp; omega
    have lk : ∀ c, 4 ≤ c → c ≤ 32 → c % 4 = 0 →
        read S.mem (0x1401120#32 + BitVec.ofNat 32 (4294967296 - c)) 4 =
          frameLookup c (read L'.mem (0x1401120#32 + BitVec.ofNat 32 (4294967296 - c)) 4)
            l8 := fun c h1 h2 h3 => by
      rw [hMk]; exact read_frameWrites _ (by decide) _ _ c hl8s h1 (by simp; omega) h3
    interval_cases i
    · exact (lk 32 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d]; simpa using ab 0#32 (by decide))
    · exact (lk 28 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d]; exact ab 4#32 (by decide))
    · exact (lk 24 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d]; exact ab 8#32 (by decide))
    · exact (lk 20 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d]; exact ab 12#32 (by decide))
    · exact (lk 16 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d]; exact ab 16#32 (by decide))
    · exact (lk 12 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d]; exact ab 20#32 (by decide))
    · exact (lk 8 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d]; exact ab 24#32 (by decide))
    · exact (lk 4 (by decide) (by decide) (by decide)).trans (by simp [frameLookup, hl8d]; exact ab 28#32 (by decide))
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
