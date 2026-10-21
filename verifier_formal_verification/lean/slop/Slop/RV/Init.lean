import Slop.RV.Memcpy
import Slop.RV.InitRuns
import Slop.Block.Block

/-! riscv_common's `boot_sequence::init` (as linked by the real Airbender guests): copies `.rodata` and `.data`
from ROM to RAM with `memcpy`. -/

namespace RV
open RV.Sym
set_option maxHeartbeats 400000

/-- `init`'s code, with the words that differ between images as parameters: `.rodata`'s ROM address into `a1`
(words 17, 18: `lui`, `addi`), `.data`'s (word 25: `lui`). -/
def initCode (w17 w18 w25 : Word) : List Word :=
  [0xff010113#32, 0x00112623#32, 0x00812423#32, 0x01010413#32, 0x00400537#32, 0x004005b7#32, 0x00058593#32,
    0x00150613#32, 0x04c5fe63#32, 0x004005b7#32, 0x00058593#32, 0x04a59a63#32, 0x01400537#32, 0x00050513#32,
    0x01400637#32, 0x39060613#32, 0x40a60633#32, w17, w18, 0x03c000ef#32, 0x01401537#32, 0x00050513#32,
    0x01401637#32, 0x00060613#32, 0x40a60633#32, w25, 0x00058593#32, 0x00c12083#32, 0x00812403#32, 0x01010113#32,
    0x0100006f#32, 0xe31ff0ef#32, 0x00410513#32, 0xe09ff0ef#32]

theorem initCode_length (w17 w18 w25 : Word) : (initCode w17 w18 w25).length = 34 := rfl

/-- The registers a block leaves alone among `x3 … x7`, `x9`, `x16 … x31` (`init`'s blocks write only `ra`, `sp`,
`s0` and `a0 … a5`). -/
theorem init_keep {σ : SState} {S0 S : State} (instrs : List Instr) (hrun : symRun instrs initState = some σ)
    (h : Rel (ctxOf S0) σ S)
    (h1 : (List.range' 3 (7 + 1 - 3)).all (fun i => (σ.reg (BitVec.ofNat 5 i)).val == i) = true)
    (h2 : (List.range' 9 (9 + 1 - 9)).all (fun i => (σ.reg (BitVec.ofNat 5 i)).val == i) = true)
    (h3 : (List.range' 16 (31 + 1 - 16)).all (fun i => (σ.reg (BitVec.ofNat 5 i)).val == i) = true)
    (i : Reg) (hi : (3 ≤ i.toNat ∧ i.toNat ≤ 7) ∨ i.toNat = 9 ∨ 16 ≤ i.toNat) : S.getReg i = S0.getReg i := by
  rcases hi with ⟨a, b⟩ | e | e
  · exact Block.regs_same_range instrs hrun h 3 7 h1 i a b
  · exact Block.regs_same_range instrs hrun h 9 9 h2 i (by omega) (by omega)
  · exact Block.regs_same_range instrs hrun h 16 31 h3 i e (by have := i.isLt; omega)

/-- `init` at `A` (with `memcpy` right after it, at `A + 136`), for any `.rodata` (912 bytes) at ROM `src` and
(empty) `.data` at ROM `dsrc`: copies `.rodata` to RAM `0x1400000`; returns to `ra` with the memory outside its
frames a block copy, ROM unchanged, and every register outside `a0 … a5` restored or untouched. Blocks: words
0 … 7, the branches at 8 and 11 (not taken), 9 … 10, 12 … 16, `.rodata`'s address (17, 18), the call (19); after
`memcpy`, 20 … 24, `.data`'s address (25), the epilogue 26 … 29, the tail call (30). -/
theorem init_run_of (w17 w18 w25 hi lo src dsrc : Word) (h17 : decode w17 = some (.lui 11#5 hi))
    (h18 : decode w18 = some (.opImm .add 11#5 11#5 lo)) (hs : hi + lo = src)
    (h25 : decode w25 = some (.lui 11#5 dsrc)) (hs4 : src.toNat % 4 = 0) (hsr : src.toNat + 912 ≤ 4194304)
    (hd4 : dsrc.toNat % 4 = 0) (hdr : dsrc.toNat ≤ 4194304)
    (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 136 + 4 * 1676 ≤ 4194304) (S : State)
    (hcode : CodeAt S A (initCode w17 w18 w25)) (hmc : CodeAt S (A + 136#32) Code.memcpy) (hpc : S.pc = A)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 32 ≤ (S.getReg 2#5).toNat)
    (hsp2 : (S.getReg 2#5).toNat ≤ 20971520) (hra : (S.getReg 1#5).toNat % 4 = 0) :
    ∃ m S', run m S = some S' ∧ S'.pc = S.getReg 1#5 ∧
      (∀ a : Word, a.toNat + 32 < (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ a.toNat →
        S'.mem a = blockCopy S.mem 20971520#32 src 912 a) ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧
      (∀ i : Reg, i ≠ 10#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 → S'.getReg i = S.getReg i) := by
  have hromL : A.toNat + 4 * (initCode w17 w18 w25).length ≤ ROM_END := by
    rw [initCode_length]; simp only [ROM_END]; omega
  have hmcr : (A + 136#32).toNat + 4 * Code.memcpy.length ≤ ROM_END := by
    rw [memcpy_length]; simp only [ROM_END]; bv_omega
  have sp16 : (S.getReg 2#5 + 4294967280#32).toNat = (S.getReg 2#5).toNat - 16 := by bv_omega
  -- words 0 … 7: `ra`, `s0` saved below `sp`, `sp -= 16`, `s0 = sp₀`, `a0 = a1 = 0x400000`, `a2 = 0x400001`
  obtain ⟨S1, hrun1, hpc1, -, hrel1, hrom1, hout1, hfr1⟩ := block_at (initCode w17 w18 w25) 0 8 IPro.instrs IPro.σ
    S A [⟨2, -8, 0, 4⟩] [] IPro.dec IPro.run (by rw [initCode_length]; omega) (by rw [hpc]; simp) hA hromL hcode
    (by sym_side) (by simp) (by decide +kernel)
  have s1sp : S1.getReg 2#5 = S.getReg 2#5 + 4294967280#32 :=
    Rel.reg_addr IPro.instrs IPro.run hrel1 2#5 2 4294967280#32 (by decide) (by decide +kernel) (by decide +kernel)
  have sv : ∀ (k : Word) (r : Nat), r < 32 → outOK IPro.σ [⟨2, -8, 0, 4⟩] [] 2 k = true →
      outNode IPro.σ 2 k = r → read S1.mem (S.getReg 2#5 + k) 4 = S.getReg (BitVec.ofNat 5 r) :=
    fun k r hr hok hn => by rw [hout1 2 k (by decide) hok, hn]; exact val_init IPro.instrs IPro.σ IPro.run S r hr
  -- the branches at 8 (`bgeu a1, a2`) and 11 (`bne a1, a0`) are not taken; words 9 … 10, 12 … 16
  have hb8 := run_branch_f hcode hA hromL hrom1 8 _ rfl (by rw [hpc1]) _ _ _ _ decode_init_04c5fe63
    (by rw [Rel.reg_cst hrel1 11#5 0x400000#32 (by decide +kernel), Rel.reg_cst hrel1 12#5 0x400001#32 (by decide +kernel)]; decide)
  obtain ⟨S2, hrun2, hpc2, -, hrel2, hrom2, -, -⟩ := block_at (initCode w17 w18 w25) 9 2 IB.instrs IB.σ
    S1.nextInstr A [] [] IB.dec IB.run (by rw [initCode_length]; omega) (by rw [next_pc, hpc1]; bv_omega) hA hromL
    (codeAt_of_rom hcode hromL hrom1) (by simp) (by simp) (by decide +kernel)
  have r2 : ∀ b : Word, b.toNat < ROM_END → S2.mem b = S.mem b := fun b hb => (hrom2 b hb).trans (hrom1 b hb)
  have hb11 := run_branch_f hcode hA hromL r2 11 _ rfl (by rw [hpc2]) _ _ _ _ decode_init_04a59a63
    (by rw [Rel.reg_cst hrel2 11#5 0x400000#32 (by decide +kernel), Rel.reg_same IB.instrs IB.run hrel2 10#5 (by decide +kernel),
      next_r, Rel.reg_cst hrel1 10#5 0x400000#32 (by decide +kernel)]; decide)
  obtain ⟨S3, hrun3, hpc3, -, hrel3, hrom3, -, -⟩ := block_at (initCode w17 w18 w25) 12 5 IC.instrs IC.σ
    S2.nextInstr A [] [] IC.dec IC.run (by rw [initCode_length]; omega) (by rw [next_pc, hpc2]; bv_omega) hA hromL
    (codeAt_of_rom hcode hromL r2) (by simp) (by simp) (by decide +kernel)
  have r3 : ∀ b : Word, b.toNat < ROM_END → S3.mem b = S.mem b := fun b hb => (hrom3 b hb).trans (r2 b hb)
  have m3 : S3.mem = S1.mem := by
    rw [Rel.mem_nil hrel3 (by decide +kernel), next_mem, Rel.mem_nil hrel2 (by decide +kernel), next_mem]
  have sp3 : S3.getReg 2#5 = S.getReg 2#5 + 4294967280#32 := by
    rw [Rel.reg_same IC.instrs IC.run hrel3 2#5 (by decide +kernel), next_r,
      Rel.reg_same IB.instrs IB.run hrel2 2#5 (by decide +kernel), next_r, s1sp]
  -- words 17, 18: `a1 = src`; 19: `jal memcpy`
  have hl17 := run_lui hcode hA hromL r3 17 _ rfl (by rw [hpc3]) _ _ h17
  have hl18 := run_addi (T := (S3.setReg 11#5 hi).nextInstr) hcode hA hromL
    (fun b hb => by rw [next_mem, set_mem]; exact r3 b hb) 18 _ rfl (by rv_regs; rw [hpc3]; bv_omega) _ _ _ h18
  obtain ⟨S4, hS4⟩ : ∃ X, X = ((S3.setReg 11#5 hi).nextInstr.setReg 11#5
      ((S3.setReg 11#5 hi).nextInstr.getReg 11#5 + lo)).nextInstr := ⟨_, rfl⟩
  rw [← hS4] at hl18
  have m4 : S4.mem = S1.mem := by rw [hS4]; simp only [next_mem, set_mem, m3]
  have r4 : ∀ b : Word, b.toNat < ROM_END → S4.mem b = S.mem b := fun b hb => by
    rw [m4, ← m3]; exact r3 b hb
  have g4 : ∀ r : Reg, r ≠ 11#5 → S4.getReg r = S3.getReg r := fun r hr => by
    by_cases h0 : r = 0#5
    · subst h0; rw [r_zero5, r_zero5]
    · rw [hS4, next_r, r_set_miss _ _ _ _ h0 hr, next_r, r_set_miss _ _ _ _ h0 hr]
  have s4_11 : S4.getReg 11#5 = src := by rw [hS4, ← hs]; rv_regs
  have hj19 := run_jal hcode hA hromL r4 19 _ rfl (by rw [hS4]; rv_regs; rw [hpc3]; bv_omega) _ _
    decode_init_03c000ef (A + 136#32) (by bv_omega) (by bv_omega)
  obtain ⟨S5, hS5⟩ : ∃ X, X = (S4.setPC (A + 136#32)).setReg 1#5 (A + BitVec.ofNat 32 (4 * 19 + 4)) := ⟨_, rfl⟩
  rw [← hS5] at hj19
  have m5 : S5.mem = S1.mem := by rw [hS5, set_mem, jump_mem, m4]
  have r5 : ∀ b : Word, b.toNat < ROM_END → S5.mem b = S.mem b := fun b hb => by
    rw [m5, ← m3]; exact r3 b hb
  have g5 : ∀ r : Reg, r ≠ 1#5 → r ≠ 11#5 → S5.getReg r = S3.getReg r := fun r h1 h11 => by
    by_cases h0 : r = 0#5
    · subst h0; rw [r_zero5, r_zero5]
    · rw [hS5, r_set_miss _ _ _ _ h0 h1, jump_r, g4 r h11]
  have sp5 : S5.getReg 2#5 = S.getReg 2#5 + 4294967280#32 := by rw [g5 _ (by decide) (by decide), sp3]
  have s5_1 : S5.getReg 1#5 = A + 80#32 := by rw [hS5]; rv_regs
  -- `memcpy(0x1400000, src, 912)`
  obtain ⟨m6, S6, hrun6, hpc6, hm6, hsp6, -, hreg6⟩ := memcpy_aligned (A + 136#32) (by bv_omega) (by bv_omega) S5
    20971520#32 src 912 (codeAt_of_rom hmc hmcr r5) (by rw [hS5]; rv_regs)
    (by rw [g5 _ (by decide) (by decide), Rel.reg_cst hrel3 10#5 0x1400000#32 (by decide +kernel)])
    (by rw [hS5, r_set_miss _ _ _ _ (by decide) (by decide), jump_r, s4_11])
    (by rw [g5 _ (by decide) (by decide), Rel.reg_cst hrel3 12#5 0x390#32 (by decide +kernel)])
    (by decide) hs4 (by decide) (by decide) (by omega) (by simp; omega)
    (by rw [sp5, sp16]; omega) (by rw [sp5, sp16]; omega) (by rw [sp5, sp16]; omega) (by rw [s5_1]; bv_omega)
    (by rw [sp5, sp16]; right; simp; omega) (by rw [sp5, sp16]; left; omega)
  -- the frame word at `sp₀ - k` (`k = 4`: `ra`, `8`: `s0`) after `memcpy`
  have fr6 : ∀ (k : Word) (r : Nat), r < 32 → outOK IPro.σ [⟨2, -8, 0, 4⟩] [] 2 k = true →
      outNode IPro.σ 2 k = r → 4294967288 ≤ k.toNat → k.toNat ≤ 4294967292 →
      read S6.mem (S.getReg 2#5 + k) 4 = S.getReg (BitVec.ofNat 5 r) := fun k r hr hok hn hk hk2 => by
    rw [hm6, read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), sp5,
      read_write_disjoint _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
      read_write_disjoint _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), m5]
    exact sv k r hr hok hn
  have r6 : ∀ b : Word, b.toNat < ROM_END → S6.mem b = S.mem b := fun b hb => by
    simp only [ROM_END] at hb
    rw [hm6, blockCopy_rom _ _ _ _ (by decide) (by decide) _ hb,
      write_rom _ _ _ _ (by rw [sp5]; simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb,
      write_rom _ _ _ _ (by rw [sp5]; simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb, r5 b hb]
  -- words 20 … 24 (`a0 = 0x1401000`, `a2 = 0`), 25 (`a1 = dsrc`), 26 … 29 (`ra`, `s0` back, `sp += 16`)
  obtain ⟨S7, hrun7, hpc7, -, hrel7, hrom7, -, -⟩ := block_at (initCode w17 w18 w25) 20 5 ID.instrs ID.σ
    S6 A [] [] ID.dec ID.run (by rw [initCode_length]; omega) (by rw [hpc6, s5_1]) hA hromL
    (codeAt_of_rom hcode hromL r6) (by simp) (by simp) (by decide +kernel)
  have r7 : ∀ b : Word, b.toNat < ROM_END → S7.mem b = S.mem b := fun b hb => (hrom7 b hb).trans (r6 b hb)
  have hl25 := run_lui hcode hA hromL r7 25 _ rfl (by rw [hpc7]) _ _ h25
  have m8 : (S7.setReg 11#5 dsrc).nextInstr.mem = S6.mem := by
    rw [next_mem, set_mem, Rel.mem_nil hrel7 (by decide +kernel)]
  have sp8 : (S7.setReg 11#5 dsrc).nextInstr.getReg 2#5 = S.getReg 2#5 + 4294967280#32 := by
    rw [next_r, r_set_miss _ _ _ _ (by decide) (by decide), Rel.reg_same ID.instrs ID.run hrel7 2#5 (by decide +kernel),
      hsp6, sp5]
  obtain ⟨S9, hrun9, hpc9, -, hrel9, hrom9, -, -⟩ := block_at (initCode w17 w18 w25) 26 4 IE.instrs IE.σ
    (S7.setReg 11#5 dsrc).nextInstr A [⟨2, 8, 16, 4⟩] [] IE.dec IE.run (by rw [initCode_length]; omega)
    (by rv_regs; rw [hpc7]; bv_omega) hA hromL (codeAt_of_rom hcode hromL (fun b hb => by rw [m8]; exact r6 b hb))
    (by have := congrArg BitVec.toNat sp8; sym_side) (by simp) (by decide +kernel)
  have m9 : S9.mem = S6.mem := by rw [Rel.mem_nil hrel9 (by decide +kernel), m8]
  have r9 : ∀ b : Word, b.toNat < ROM_END → S9.mem b = S.mem b := fun b hb => by rw [m9]; exact r6 b hb
  have s9_1 : S9.getReg 1#5 = S.getReg 1#5 := by
    rw [Rel.reg_load IE.instrs IE.run hrel9 1#5 2 12#32 (by decide) (by decide +kernel) (by decide +kernel), m8,
      sp8, BitVec.add_assoc]
    exact fr6 _ 1 (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  have s9_8 : S9.getReg 8#5 = S.getReg 8#5 := by
    rw [Rel.reg_load IE.instrs IE.run hrel9 8#5 2 8#32 (by decide) (by decide +kernel) (by decide +kernel), m8,
      sp8, BitVec.add_assoc]
    exact fr6 _ 8 (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  have s9_2 : S9.getReg 2#5 = S.getReg 2#5 := by
    rw [Rel.reg_addr IE.instrs IE.run hrel9 2#5 2 16#32 (by decide) (by decide +kernel) (by decide +kernel), sp8]
    bv_omega
  -- word 30: the tail call `memcpy(0x1401000, dsrc, 0)`, which returns to `ra`
  have hj30 := run_jal hcode hA hromL r9 30 _ rfl (by rw [hpc9]) _ _ decode_init_0100006f (A + 136#32) (by bv_omega)
    (by bv_omega)
  obtain ⟨S10, hS10⟩ : ∃ X, X = (S9.setPC (A + 136#32)).setReg 0#5 (A + BitVec.ofNat 32 (4 * 30 + 4)) := ⟨_, rfl⟩
  rw [← hS10] at hj30
  have g10 : ∀ r, S10.getReg r = S9.getReg r := fun r => by rw [hS10]; exact x0_getReg _ _ _ r
  have m10 : S10.mem = S6.mem := by rw [hS10, set_mem, jump_mem, m9]
  obtain ⟨m11, S11, hrun11, hpc11, hm11, -, -, hreg11⟩ := memcpy_aligned (A + 136#32) (by bv_omega) (by bv_omega) S10
    20975616#32 dsrc 0 (codeAt_of_rom hmc hmcr (fun b hb => by rw [m10]; exact r6 b hb)) (by rw [hS10]; rfl)
    (by rw [g10, Rel.reg_same IE.instrs IE.run hrel9 10#5 (by decide +kernel), next_r,
      r_set_miss _ _ _ _ (by decide) (by decide), Rel.reg_cst hrel7 10#5 0x1401000#32 (by decide +kernel)])
    (by rw [g10, Rel.reg_addr IE.instrs IE.run hrel9 11#5 11 0#32 (by decide) (by decide +kernel) (by decide +kernel),
      next_r, r_set_hit _ _ _ (by decide), BitVec.add_zero])
    (by rw [g10, Rel.reg_same IE.instrs IE.run hrel9 12#5 (by decide +kernel), next_r,
      r_set_miss _ _ _ _ (by decide) (by decide), Rel.reg_cst hrel7 12#5 0#32 (by decide +kernel)])
    (by decide) hd4 (by decide) (by decide) (by omega) (by simp; omega)
    (by rw [g10, s9_2]; exact hsp) (by rw [g10, s9_2]; omega) (by rw [g10, s9_2]; omega) (by rw [g10, s9_1]; exact hra)
    (by rw [g10, s9_2]; right; simp; omega) (by rw [g10, s9_2]; left; simp; omega)
  have sp10 : S10.getReg 2#5 = S.getReg 2#5 := by rw [g10, s9_2]
  refine ⟨_, S11, run_trans hrun1 (run_trans hb8 (run_trans hrun2 (run_trans hb11 (run_trans hrun3 (run_trans hl17
    (run_trans hl18 (run_trans hj19 (run_trans hrun6 (run_trans hrun7 (run_trans hl25 (run_trans hrun9
    (run_trans hj30 hrun11)))))))))))), by rw [hpc11, g10, s9_1], ?_, ?_, ?_⟩
  · -- memory outside the frames: `.rodata` copied
    intro a ha
    rw [hm11, blockCopy_zero, sp10, write_outside _ _ _ _ _ (by bv_omega) (by bv_omega),
      write_outside _ _ _ _ _ (by bv_omega) (by bv_omega), m10, hm6, sp5]
    simp only [blockCopy]
    split
    · rw [write_rom _ _ _ _ (by simp only [writable, ROM_END, RAM_END]; bv_omega) _ (by simp only [ROM_END]; bv_omega),
        write_rom _ _ _ _ (by simp only [writable, ROM_END, RAM_END]; bv_omega) _ (by simp only [ROM_END]; bv_omega),
        r5 _ (by simp only [ROM_END]; bv_omega)]
    · rw [write_outside _ _ _ _ _ (by bv_omega) (by bv_omega), write_outside _ _ _ _ _ (by bv_omega) (by bv_omega), m5]
      exact out_frame hfr1 ⟨2, -8, 0, 1⟩ (by decide +kernel) (by decide) (by sym_side) a
        (by simp only [Region.Outside]; omega)
  · intro b hb
    rw [hm11, blockCopy_zero, write_rom _ _ _ _ (by rw [sp10]; simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb,
      write_rom _ _ _ _ (by rw [sp10]; simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb, m10]
    exact r6 b hb
  · intro i h10 h11 h12 h13 h14 h15
    rw [hreg11 i h11 h12 h13 h14 h15, g10]
    by_cases e1 : i = 1#5
    · subst e1; exact s9_1
    by_cases e2 : i = 2#5
    · subst e2; exact s9_2
    by_cases e8 : i = 8#5
    · subst e8; exact s9_8
    by_cases e0 : i = 0#5
    · subst e0; rw [r_zero5, r_zero5]
    have hi : (3 ≤ i.toNat ∧ i.toNat ≤ 7) ∨ i.toNat = 9 ∨ 16 ≤ i.toNat := by bv_omega
    rw [init_keep IE.instrs IE.run hrel9 (by decide +kernel) (by decide +kernel) (by decide +kernel) i hi, next_r,
      r_set_miss _ _ _ _ e0 h11, init_keep ID.instrs ID.run hrel7 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) i hi, hreg6 i h11 h12 h13 h14 h15, g5 i e1 h11,
      init_keep IC.instrs IC.run hrel3 (by decide +kernel) (by decide +kernel) (by decide +kernel) i hi, next_r,
      init_keep IB.instrs IB.run hrel2 (by decide +kernel) (by decide +kernel) (by decide +kernel) i hi, next_r,
      init_keep IPro.instrs IPro.run hrel1 (by decide +kernel) (by decide +kernel) (by decide +kernel) i hi]

/-- `init` at `A` (with `memcpy` right after it, at `A + 136`): copies `.rodata` (912 bytes, from ROM `0x4334`
to RAM `0x1400000`) and its empty `.data`; returns to `ra` with the memory outside its frames a block copy,
ROM unchanged, and every register outside `a0 … a5` restored or untouched. -/
theorem init_run (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 136 + 4 * 1676 ≤ 4194304) (S : State)
    (hcode : CodeAt S A Code.init) (hmc : CodeAt S (A + 136#32) Code.memcpy) (hpc : S.pc = A)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 32 ≤ (S.getReg 2#5).toNat)
    (hsp2 : (S.getReg 2#5).toNat ≤ 20971520) (hra : (S.getReg 1#5).toNat % 4 = 0) :
    ∃ m S', run m S = some S' ∧ S'.pc = S.getReg 1#5 ∧
      (∀ a : Word, a.toNat + 32 < (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ a.toNat →
        S'.mem a = blockCopy S.mem 20971520#32 17204#32 912 a) ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧
      (∀ i : Reg, i ≠ 10#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 → S'.getReg i = S.getReg i) :=
  init_run_of 0x000045b7#32 0x33458593#32 0x000065b7#32 0x00004000#32 0x334#32 17204#32 24576#32 rfl rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) A hA hAr S hcode hmc hpc hsp hsp1 hsp2 hra

end RV
