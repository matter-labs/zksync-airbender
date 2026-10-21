import Slop.RV.CallW
import Slop.RV.Blake.Values

/-! `blake2s_compress(st, len, last)`: the call contract, from the symbolic run (`Block`) and the values (`Values`). -/

namespace RV
open _root_.RV.Sym
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

/-- `n` words at `p`. -/
def wordsAt (m : Word → BitVec 8) (p : Word) (n : Nat) : Vector Word n :=
  Vector.ofFn fun i => read m (p + BitVec.ofNat 32 (4 * i.val)) 4

/-- `blake2s_compress(st = a0, len = a1, last = a2)`: the evaluator (state +0, block +64, counter +128) 4-aligned in RAM
above `sp`, `last` a `bool`. -/
def blakePre (s : State) : Prop :=
  (s.getReg 10#5).toNat % 4 = 0 ∧ (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat ∧
  (s.getReg 10#5).toNat + 132 ≤ RAM_END ∧ (s.getReg 12#5 = 0#32 ∨ s.getReg 12#5 = 1#32)

/-- The state becomes the compression of the block, with the counter advanced by `len`. -/
def blakePost (s s' : State) : Prop :=
  wordsAt s'.mem (s.getReg 10#5) 8 =
    Spec.compress (wordsAt s.mem (s.getReg 10#5) 8) (wordsAt s.mem (s.getReg 10#5 + 64#32) 16)
      (read s.mem (s.getReg 10#5 + 128#32) 4 + s.getReg 11#5) (s.getReg 12#5 = 1#32) ∧
  read s'.mem (s.getReg 10#5 + 128#32) 4 = read s.mem (s.getReg 10#5 + 128#32) 4 + s.getReg 11#5

namespace Blake
abbrev rSp : Region := ⟨2, -160, 0, 16⟩
abbrev rSt : Region := ⟨10, 0, 132, 4⟩
end Blake
open Blake

attribute [local irreducible] RV.Sym.Pool.val in
theorem blake2s_compress_impl (A : Word) :
    ImplementsAtW A Code.blake2s_compress [] 160 blakePre 132 blakePost := by
  intro s _ _ hcall hpre
  simp only [blakePre, RAM_END] at hpre
  obtain ⟨h4, hsp, hR, hl⟩ := hpre
  rw [Blake.ret] at hcall
  have hsp' : ROM_END + 160 ≤ (s.getReg 2#5).toNat ∧ (s.getReg 2#5).toNat % 16 = 0 :=
    ⟨hcall.2.2.2.2.2.1, hcall.2.2.2.2.1⟩
  simp only [ROM_END] at hsp'
  apply returnsW_of_sym _ Blake.instrs Blake.σ s 160 132 [rSp, rSt] [(rSp, rSt)] _ Blake.dec Blake.run hcall
  all_goals first | decide +kernel | sym_side | skip
  intro S' _ hout
  set c := ctxOf s
  -- the loads and the registers
  have ld : ∀ i (k : Word), i < Blake.σ.pool.len → nodeAt Blake.σ.pool i = .load 4 true 10 k →
      Blake.σ.pool.val c i = read s.mem (s.getReg 10#5 + k) 4 :=
    fun i k hi h => load_val _ _ Blake.run s i 10 k true (by decide) hi h
  have r11 : Blake.σ.pool.val c 11 = s.getReg 11#5 := val_init _ _ Blake.run s 11 (by decide)
  have r12 : Blake.σ.pool.val c 12 = s.getReg 12#5 := val_init _ _ Blake.run s 12 (by decide)
  have vals := Blake.values c (by rw [r12]; exact hl)
  have ht := Blake.t2 c
  have o : ∀ k, outOK Blake.σ [rSp, rSt] [(rSp, rSt)] 10 k = true →
      read S'.mem (s.getReg 10#5 + k) 4 = Blake.σ.pool.val c (outNode Blake.σ 10 k) :=
    fun k h => hout 10 k (by decide) h
  have hH : Blake.H c = wordsAt s.mem (s.getReg 10#5) 8 := by
    apply Vector.ext; intro i hi
    simp only [wordsAt, Vector.getElem_ofFn]
    interval_cases i
    · exact ld 37 _ (by decide +kernel) (by decide +kernel)
    · exact ld 38 _ (by decide +kernel) (by decide +kernel)
    · exact ld 39 _ (by decide +kernel) (by decide +kernel)
    · exact ld 40 _ (by decide +kernel) (by decide +kernel)
    · exact ld 36 _ (by decide +kernel) (by decide +kernel)
    · exact ld 43 _ (by decide +kernel) (by decide +kernel)
    · exact ld 44 _ (by decide +kernel) (by decide +kernel)
    · exact ld 45 _ (by decide +kernel) (by decide +kernel)
  have hM : Blake.M c = wordsAt s.mem (s.getReg 10#5 + 64#32) 16 := by
    apply Vector.ext; intro i hi
    simp only [wordsAt, Vector.getElem_ofFn, BitVec.add_assoc, BitVec.reduceAdd]
    interval_cases i
    · exact ld 41 _ (by decide +kernel) (by decide +kernel)
    · exact ld 48 _ (by decide +kernel) (by decide +kernel)
    · exact ld 49 _ (by decide +kernel) (by decide +kernel)
    · exact ld 50 _ (by decide +kernel) (by decide +kernel)
    · exact ld 102 _ (by decide +kernel) (by decide +kernel)
    · exact ld 108 _ (by decide +kernel) (by decide +kernel)
    · exact ld 109 _ (by decide +kernel) (by decide +kernel)
    · exact ld 110 _ (by decide +kernel) (by decide +kernel)
    · exact ld 157 _ (by decide +kernel) (by decide +kernel)
    · exact ld 162 _ (by decide +kernel) (by decide +kernel)
    · exact ld 163 _ (by decide +kernel) (by decide +kernel)
    · exact ld 164 _ (by decide +kernel) (by decide +kernel)
    · exact ld 212 _ (by decide +kernel) (by decide +kernel)
    · exact ld 217 _ (by decide +kernel) (by decide +kernel)
    · exact ld 218 _ (by decide +kernel) (by decide +kernel)
    · exact ld 219 _ (by decide +kernel) (by decide +kernel)
  have h35 : Blake.σ.pool.val c 35 = read s.mem (s.getReg 10#5 + 128#32) 4 :=
    ld _ _ (by decide +kernel) (by decide +kernel)
  refine ⟨?_, ?_⟩
  · rw [hH.symm, hM.symm, ← h35, ← r11, ← r12, ← vals]
    apply Vector.ext; intro i hi
    simp only [wordsAt, Vector.getElem_ofFn]
    interval_cases i
    · exact (o _ (by decide +kernel)).trans (by rw [show outNode Blake.σ 10 (BitVec.ofNat 32 (4 * 0)) = 1383 by decide +kernel]; rfl)
    · exact (o _ (by decide +kernel)).trans (by rw [show outNode Blake.σ 10 (BitVec.ofNat 32 (4 * 1)) = 1384 by decide +kernel]; rfl)
    · exact (o _ (by decide +kernel)).trans (by rw [show outNode Blake.σ 10 (BitVec.ofNat 32 (4 * 2)) = 1387 by decide +kernel]; rfl)
    · exact (o _ (by decide +kernel)).trans (by rw [show outNode Blake.σ 10 (BitVec.ofNat 32 (4 * 3)) = 1388 by decide +kernel]; rfl)
    · exact (o _ (by decide +kernel)).trans (by rw [show outNode Blake.σ 10 (BitVec.ofNat 32 (4 * 4)) = 1391 by decide +kernel]; rfl)
    · exact (o _ (by decide +kernel)).trans (by rw [show outNode Blake.σ 10 (BitVec.ofNat 32 (4 * 5)) = 1392 by decide +kernel]; rfl)
    · exact (o _ (by decide +kernel)).trans (by rw [show outNode Blake.σ 10 (BitVec.ofNat 32 (4 * 6)) = 1395 by decide +kernel]; rfl)
    · exact (o _ (by decide +kernel)).trans (by rw [show outNode Blake.σ 10 (BitVec.ofNat 32 (4 * 7)) = 1396 by decide +kernel]; rfl)
  · rw [o _ (by decide +kernel), show outNode Blake.σ 10 128#32 = 42 by decide +kernel, ht, h35, r11]

end RV
