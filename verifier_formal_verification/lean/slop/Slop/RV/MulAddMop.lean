import Slop.RV.Ext4Call
import Slop.RV.Code.ext4_mul_add_mop
import Slop.Sym.Meta

/-! `ext4_mul_add` with the field opcodes (feature `mop`): `mul_assign_flat_impl_fma` and the add, inlined.
By the symbolic executor: one kernel run of the body, then the four stored limbs as terms. -/

namespace RV
open _root_.RV.Sym
set_option maxHeartbeats 0

sym_block MulAddMop := Code.ext4_mul_add_mop

namespace MulAddMop
abbrev rSp : Region := ⟨2, -16, 0, 16⟩
abbrev rA0 : Region := ⟨10, 0, 16, 4⟩
abbrev rA1 : Region := ⟨11, 0, 16, 4⟩
abbrev rA2 : Region := ⟨12, 0, 16, 4⟩
end MulAddMop
open MulAddMop

/-- `acc ← acc · x + c` (`mulAddPost`), anywhere in ROM. -/
theorem ext4_mul_add_mop_impl (A : Word) :
    ImplementsAtW A Code.ext4_mul_add_mop [] 16 mulAddPre 16 mulAddPost := by
  intro s _ _ hcall hpre
  simp only [mulAddPre, argOk, disj16, RAM_END] at hpre
  obtain ⟨⟨ha4, hasp, haR⟩, ⟨hx4, hxsp, hxR⟩, ⟨hc4, hcsp, hcR⟩, hax, hac, -, -, -⟩ := hpre
  rw [MulAddMop.ret] at hcall
  have hsp : ROM_END + 16 ≤ (s.getReg 2#5).toNat ∧ (s.getReg 2#5).toNat % 16 = 0 :=
    ⟨hcall.2.2.2.2.2.1, hcall.2.2.2.2.1⟩
  simp only [ROM_END] at hsp
  apply returnsW_of_sym _ MulAddMop.instrs MulAddMop.σ s 16 16 [rSp, rA0, rA1, rA2]
    [(rSp, rA0), (rSp, rA1), (rSp, rA2), (rA0, rA1), (rA0, rA2)] _ MulAddMop.dec MulAddMop.run hcall
  all_goals first | decide +kernel | sym_side | skip
  intro S' _ hout
  have o0 := hout 10 0#32 (by decide) (by decide +kernel)
  have o1 := hout 10 4#32 (by decide) (by decide +kernel)
  have o2 := hout 10 8#32 (by decide) (by decide +kernel)
  have o3 := hout 10 12#32 (by decide) (by decide +kernel)
  rw [show s.getReg 10#5 + 0#32 = s.getReg 10#5 by simp] at o0
  simp only [mulAddPost, canon4, e4At]
  rw [o0, o1, o2, o3]
  sym_unfold
  simp only [ctxOf, sext_word, ite_self, BitVec.add_zero]
  generalize read s.mem (s.getReg 10#5) 4 = a0
  generalize read s.mem (s.getReg 10#5 + 4#32) 4 = a1
  generalize read s.mem (s.getReg 10#5 + 8#32) 4 = a2
  generalize read s.mem (s.getReg 10#5 + 12#32) 4 = a3
  generalize read s.mem (s.getReg 11#5) 4 = b0
  generalize read s.mem (s.getReg 11#5 + 4#32) 4 = b1
  generalize read s.mem (s.getReg 11#5 + 8#32) 4 = b2
  generalize read s.mem (s.getReg 11#5 + 12#32) 4 = b3
  generalize read s.mem (s.getReg 12#5) 4 = c0
  generalize read s.mem (s.getReg 12#5 + 4#32) 4 = c1
  generalize read s.mem (s.getReg 12#5 + 8#32) 4 = c2
  generalize read s.mem (s.getReg 12#5 + 12#32) 4 = c3
  refine ⟨⟨mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun,
    mopVal_lt _ _ _ _ nofun⟩, ?_⟩
  simp only [e4, mont_add, mont_fma, mont_mul, mont_nonres, Spec.ofLimbs_mul, Spec.ofLimbs_add]
  congr 1 <;> ring
end RV
