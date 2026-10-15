import Slop.RV.Ext4Call
import Slop.RV.MulAdd.Values

/-! `ext4_mul_add` in plain Rust: the call contract, from the symbolic run (`Block`) and the values of the four stored
limbs (`Values`). -/

namespace RV
open _root_.RV.Sym
set_option maxHeartbeats 0

namespace MulAdd
abbrev rSp : Region := ⟨2, -80, 0, 16⟩
abbrev rA0 : Region := ⟨10, 0, 16, 4⟩
abbrev rA1 : Region := ⟨11, 0, 16, 4⟩
abbrev rA2 : Region := ⟨12, 0, 16, 4⟩
end MulAdd
open MulAdd

/-- `acc ← acc · x + c` (`mulAddPost`), anywhere in ROM. -/
theorem ext4_mul_add_impl (A : Word) :
    ImplementsAtW A Code.ext4_mul_add [] 80 mulAddPre 16 mulAddPost := by
  intro s _ _ hcall hpre
  simp only [mulAddPre, argOk, disj16, RAM_END] at hpre
  obtain ⟨⟨ha4, hasp, haR⟩, ⟨hx4, hxsp, hxR⟩, ⟨hc4, hcsp, hcR⟩, hax, hac, hca, hcx, hcc⟩ := hpre
  rw [MulAdd.ret] at hcall
  have hsp : ROM_END + 80 ≤ (s.getReg 2#5).toNat ∧ (s.getReg 2#5).toNat % 16 = 0 :=
    ⟨hcall.2.2.2.2.2.1, hcall.2.2.2.2.1⟩
  simp only [ROM_END] at hsp
  apply returnsW_of_sym _ MulAdd.instrs MulAdd.σ s 80 16 [rSp, rA0, rA1, rA2]
    [(rSp, rA0), (rSp, rA1), (rSp, rA2), (rA0, rA1), (rA0, rA2)] _ MulAdd.dec MulAdd.run hcall
  all_goals first | decide +kernel | sym_side | skip
  intro S' _ hout
  have ld : ∀ i b (k : Word), b < 32 → i < MulAdd.σ.pool.len → nodeAt MulAdd.σ.pool i = .load 4 true b k →
      MulAdd.σ.pool.val (ctxOf s) i = read s.mem (s.getReg (BitVec.ofNat 5 b) + k) 4 :=
    fun i b k hb hi h => load_val _ _ MulAdd.run s i b k true hb hi h
  have z : ∀ r : Reg, s.getReg r + 0#32 = s.getReg r := fun r => by simp
  have l35 := ld 35 10 0#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l36 := ld 36 10 4#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l37 := ld 37 10 8#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l38 := ld 38 10 12#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l34 := ld 34 11 0#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l39 := ld 39 11 4#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l40 := ld 40 11 8#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l41 := ld 41 11 12#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l335 := ld 335 12 0#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l336 := ld 336 12 4#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l341 := ld 341 12 8#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l342 := ld 342 12 12#32 (by decide) (by decide +kernel) (by decide +kernel)
  simp only [z] at l35 l34 l335
  simp only [canon4] at hca hcx hcc
  obtain ⟨b0, b1, b2, b3, hv⟩ := MulAdd.values (ctxOf s)
    (by rw [l35]; exact hca.1) (by rw [l36]; exact hca.2.1) (by rw [l37]; exact hca.2.2.1) (by rw [l38]; exact hca.2.2.2)
    (by rw [l34]; exact hcx.1) (by rw [l39]; exact hcx.2.1) (by rw [l40]; exact hcx.2.2.1) (by rw [l41]; exact hcx.2.2.2)
    (by rw [l335]; exact hcc.1) (by rw [l336]; exact hcc.2.1) (by rw [l341]; exact hcc.2.2.1)
    (by rw [l342]; exact hcc.2.2.2)
  have o0 := hout 10 0#32 (by decide) (by decide +kernel)
  have o1 := hout 10 4#32 (by decide) (by decide +kernel)
  have o2 := hout 10 8#32 (by decide) (by decide +kernel)
  have o3 := hout 10 12#32 (by decide) (by decide +kernel)
  rw [show outNode MulAdd.σ 10 0#32 = 353 by decide +kernel] at o0
  rw [show outNode MulAdd.σ 10 4#32 = 354 by decide +kernel] at o1
  rw [show outNode MulAdd.σ 10 8#32 = 365 by decide +kernel] at o2
  rw [show outNode MulAdd.σ 10 12#32 = 366 by decide +kernel] at o3
  simp only [z] at o0
  simp only [mulAddPost, canon4, e4At]
  rw [o0, o1, o2, o3]
  refine ⟨⟨b0, b1, b2, b3⟩, ?_⟩
  rw [hv, l35, l36, l37, l38, l34, l39, l40, l41, l335, l336, l341, l342]
end RV
