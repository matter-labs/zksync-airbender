import Slop.RV.Tactic
import Slop.RV.Copy

/-! Running copy code: `j` load/store pairs extend a block copy by `4j` bytes (general in registers, offsets, the
code's address and `j`), and code in ROM survives copies into RAM. -/

set_option linter.deprecated false

namespace RV
set_option maxHeartbeats 0

/-- `j` pairs `lw rT, o+4i(rS)` / `sw rT, o+4i(rD)` (at `X + 8i`, `X + 8i + 4`) copy words `o … o+4j` of a block
copy from `q` (in `rS`) to `p` (in `rD`); only `rT` changes among the registers. -/
theorem run_copy_pairs (rT rS rD : Reg) (hT : rT ≠ 0) (hS0 : rS ≠ 0) (hD0 : rD ≠ 0) (hTS : rT ≠ rS) (hTD : rT ≠ rD) (N : Word → BitVec 8)
    (p q : Word) (j : Nat) : ∀ (S : State) (X : Word) (o : Nat),
    S.pc = X → X.toNat % 4 = 0 → X.toNat + 8 * j ≤ ROM_END →
    (∀ i < j, decode (read S.mem (X + BitVec.ofNat 32 (8 * i)) 4) = some (.load 4 true rT rS (BitVec.ofNat 32 (o + 4 * i))) ∧
      decode (read S.mem (X + BitVec.ofNat 32 (8 * i + 4)) 4) = some (.store 4 rT rD (BitVec.ofNat 32 (o + 4 * i)))) →
    S.getReg rS = q → S.getReg rD = p → S.mem = blockCopy N p q o →
    p.toNat % 4 = 0 → q.toNat % 4 = 0 → o % 4 = 0 → ROM_END ≤ p.toNat → p.toNat + o + 4 * j ≤ RAM_END →
    q.toNat + o + 4 * j ≤ RAM_END → (q.toNat + o + 4 * j ≤ p.toNat ∨ p.toNat + o + 4 * j ≤ q.toNat) →
    ∃ S', run (2 * j) S = some S' ∧ S'.pc = X + BitVec.ofNat 32 (8 * j) ∧ S'.mem = blockCopy N p q (o + 4 * j) ∧
      ∀ r, r ≠ rT → S'.getReg r = S.getReg r := by
  induction j with
  | zero =>
    intro S X o hpc _ _ _ _ _ hm _ _ _ _ _ _ _
    exact ⟨S, rfl, by simp [hpc], by simpa using hm, fun _ _ => rfl⟩
  | succ j ih =>
    intro S X o hpc hX hXr hcode hS hD hm hp hq ho hpr hpe hqe hdisj
    simp only [ROM_END, RAM_END] at hXr hpr hpe hqe
    obtain ⟨hl, hs⟩ := hcode 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, BitVec.add_zero, Nat.zero_add] at hl hs
    rw [show X + BitVec.ofNat 32 4 = X + 4 from rfl] at hs
    -- the load
    have st1 : step S = some (S.setReg rT (read S.mem (q + BitVec.ofNat 32 o) 4)).nextInstr := by
      rw [step_ok S (by rw [hpc]; exact hX) (by rw [hpc]; simp only [ROM_END]; omega), hpc, hl, Option.bind_some,
        exec_load _ _ _ _ _ _ hT (by rw [hS]; simp only [aligned]; bv_omega)
          (by rw [hS]; simp only [readable, RAM_END]; bv_omega), if_pos rfl, sext_word, hS]
    -- the store
    have hD1 : ((S.setReg rT (read S.mem (q + BitVec.ofNat 32 o) 4)).nextInstr).getReg rD = p := by
      simp only [next_r]; rw [r_set_miss _ _ _ _ hD0 (Ne.symm hTD), hD]
    have st2 : step (S.setReg rT (read S.mem (q + BitVec.ofNat 32 o) 4)).nextInstr =
        some (((S.setReg rT (read S.mem (q + BitVec.ofNat 32 o) 4)).nextInstr).store (p + BitVec.ofNat 32 o)
          (read S.mem (q + BitVec.ofNat 32 o) 4) 4).nextInstr := by
      rw [step_ok _ (by simp only [next_pc, set_pc, hpc]; bv_omega) (by simp only [next_pc, set_pc, hpc, ROM_END]; bv_omega)]
      simp only [next_pc, set_pc, next_mem, set_mem, hpc]
      rw [hs, Option.bind_some, exec_store _ _ _ _ _ (by rw [hD1]; simp only [aligned]; bv_omega)
        (by rw [hD1]; simp only [writable, ROM_END, RAM_END]; bv_omega), hD1, next_r, r_set_hit _ _ _ hT]
    -- the state after the pair
    obtain ⟨S2, hS2⟩ : ∃ S2, S2 = (((S.setReg rT (read S.mem (q + BitVec.ofNat 32 o) 4)).nextInstr).store
        (p + BitVec.ofNat 32 o) (read S.mem (q + BitVec.ofNat 32 o) 4) 4).nextInstr := ⟨_, rfl⟩
    rw [← hS2] at st2
    have hm2 : S2.mem = blockCopy N p q (o + 4) := by
      simp only [hS2, next_mem, store_mem, set_mem, hm]
      rw [read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)]
      exact copy_step N p q o 4 (by omega) (by omega)
    have hpc2 : S2.pc = X + 8 := by simp only [hS2, next_pc, store_pc, set_pc, hpc]; bv_omega
    have hreg2 : ∀ r, r ≠ rT → S2.getReg r = S.getReg r := by
      intro r hr
      simp only [hS2, next_r, store_r]
      by_cases h0 : r = 0
      · subst h0; rw [r_zero, r_zero]
      · rw [r_set_miss _ _ _ _ h0 hr]
    have hcode2 : ∀ i < j, decode (read S2.mem (X + 8 + BitVec.ofNat 32 (8 * i)) 4) =
          some (.load 4 true rT rS (BitVec.ofNat 32 (o + 4 + 4 * i))) ∧
        decode (read S2.mem (X + 8 + BitVec.ofNat 32 (8 * i + 4)) 4) =
          some (.store 4 rT rD (BitVec.ofNat 32 (o + 4 + 4 * i))) := by
      intro i hi
      obtain ⟨hli, hsi⟩ := hcode (i + 1) (by omega)
      simp only [hS2, next_mem, store_mem, set_mem]
      rw [read_write_rom _ _ _ _ _ (by simp only [ROM_END]; bv_omega) (by simp only [writable, ROM_END, RAM_END]; bv_omega),
        read_write_rom _ _ _ _ _ (by simp only [ROM_END]; bv_omega) (by simp only [writable, ROM_END, RAM_END]; bv_omega)]
      rw [show X + 8 + BitVec.ofNat 32 (8 * i) = X + BitVec.ofNat 32 (8 * (i + 1)) by bv_omega,
        show X + 8 + BitVec.ofNat 32 (8 * i + 4) = X + BitVec.ofNat 32 (8 * (i + 1) + 4) by bv_omega,
        show o + 4 + 4 * i = o + 4 * (i + 1) by omega]
      exact ⟨hli, hsi⟩
    obtain ⟨S', hrun, hpc', hm', hregs⟩ := ih S2 (X + 8) (o + 4) hpc2 (by bv_omega)
      (by simp only [ROM_END]; bv_omega) hcode2 (by rw [hreg2 _ (Ne.symm hTS), hS]) (by rw [hreg2 _ (Ne.symm hTD), hD])
      hm2 hp hq (by omega) (by simp only [ROM_END]; omega) (by simp only [RAM_END]; omega)
      (by simp only [RAM_END]; omega) (by omega)
    refine ⟨S', ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, run_succ, st1, Option.bind_some, run_succ, st2,
        Option.bind_some, hrun]
    · rw [hpc']; bv_omega
    · rw [hm', show o + 4 + 4 * j = o + 4 * (j + 1) by omega]
    · intro r hr; rw [hregs r hr, hreg2 r hr]

/-- Code in ROM is not affected by a block copy into RAM. -/
theorem codeAt_blockCopy {S S' : State} {A : Word} {code : List Word} {d s : Word} {len : Nat}
    (hc : CodeAt S A code) (hm : S'.mem = blockCopy S.mem d s len) (hA : A.toNat + 4 * code.length ≤ ROM_END)
    (hd : ROM_END ≤ d.toNat) (hd2 : d.toNat + len ≤ 2 ^ 32) : CodeAt S' A code := by
  intro i hi
  rw [hm, read_blockCopy_outside _ _ _ _ _ _ (by simp only [ROM_END] at *; bv_omega) (by simp only [ROM_END] at *; bv_omega) hd2]
  exact hc i hi

/-- `CodeAt` only depends on the memory. -/
theorem codeAt_mem_eq {S S' : State} {A : Word} {code : List Word} (hm : S'.mem = S.mem) (hc : CodeAt S A code) :
    CodeAt S' A code := fun i hi => by rw [hm]; exact hc i hi

/-- Code in ROM survives anything that leaves ROM bytes unchanged. -/
theorem codeAt_of_rom {S S' : State} {A : Word} {code : List Word} (hc : CodeAt S A code)
    (hA : A.toNat + 4 * code.length ≤ ROM_END) (hm : ∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) :
    CodeAt S' A code := by
  intro i hi
  rw [read_congr S'.mem S.mem _ 4 (fun j hj => hm _ (by simp only [ROM_END] at *; bv_omega))]
  exact hc i hi

/-- A block copy into RAM leaves ROM bytes unchanged. -/
theorem blockCopy_rom (m : Word → BitVec 8) (d s : Word) (len : Nat) (hd : ROM_END ≤ d.toNat)
    (hd2 : d.toNat + len ≤ 2 ^ 32) (b : Word) (hb : b.toNat < ROM_END) : blockCopy m d s len b = m b :=
  blockCopy_outside _ _ _ _ _ (by simp only [ROM_END] at *; bv_omega)

/-- A store into RAM leaves ROM bytes unchanged. -/
theorem write_rom (m : Word → BitVec 8) (a v : Word) (n : Nat) (ha : writable a n) (b : Word) (hb : b.toNat < ROM_END) :
    write m a v n b = m b :=
  write_outside _ _ _ _ _ (by simp only [writable, ROM_END, RAM_END] at *; omega)
    (by simp only [writable, ROM_END, RAM_END] at *; omega)

/-- Reads of two memories at two addresses agree if their bytes do. -/
theorem read_congr2 (m m' : Word → BitVec 8) (a a' : Word) (k : Nat)
    (h : ∀ j < k, m' (a' + BitVec.ofNat 32 j) = m (a + BitVec.ofNat 32 j)) : read m' a' k = read m a k := by
  induction k generalizing a a' with
  | zero => rfl
  | succ k ih =>
    simp only [read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih]
    intro j hj
    have := h (j + 1) (by omega)
    rwa [show a' + 1 + BitVec.ofNat 32 j = a' + BitVec.ofNat 32 (j + 1) by bv_omega,
      show a + 1 + BitVec.ofNat 32 j = a + BitVec.ofNat 32 (j + 1) by bv_omega]

/-- A table copied by a block copy: found at the destination. -/
theorem codeAt_blockCopy_dst {S S' : State} {s0 d : Word} {C : List Word} {n : Nat} (hc : CodeAt S s0 C)
    (hm : ∀ a : Word, (a - d).toNat < n → S'.mem a = blockCopy S.mem d s0 n a) (hn : 4 * C.length ≤ n)
    (hd : d.toNat + n ≤ 2 ^ 32) : CodeAt S' d C := by
  intro i hi
  rw [← hc i hi]
  apply read_congr2
  intro j hj
  rw [hm _ (by bv_omega)]
  simp only [blockCopy]
  rw [if_pos (by bv_omega)]
  congr 1; bv_omega

/-- A table at offset `o` of a copied block, at the same offset in the copy. -/
theorem codeMem_blockCopy_off {S : State} {m' : Word → BitVec 8} {s0 d : Word} {C : List Word} {n o : Nat}
    (hc : CodeAt S (s0 + BitVec.ofNat 32 o) C)
    (hm : ∀ a : Word, (a - d).toNat < n → m' a = blockCopy S.mem d s0 n a) (hn : o + 4 * C.length ≤ n)
    (hd : d.toNat + n ≤ 2 ^ 32) (hs : s0.toNat + n ≤ 2 ^ 32) : CodeMem m' (d + BitVec.ofNat 32 o) C := by
  intro i hi
  rw [← hc i hi]
  apply read_congr2
  intro j hj
  rw [hm _ (by bv_omega)]
  simp only [blockCopy]
  rw [if_pos (by bv_omega)]
  congr 1; bv_omega

end RV
