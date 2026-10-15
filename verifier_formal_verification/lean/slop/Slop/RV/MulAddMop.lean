import Slop.RV.Ext4Call
import Slop.RV.Code.ext4_mul_add_mop

/-! `ext4_mul_add` with the field opcodes (feature `mop`): `mul_assign_flat_impl_fma` and the add, inlined. -/

namespace RV
set_option maxHeartbeats 0

/-- `acc ← acc · x + c` (`mulAddPost`), anywhere in ROM. -/
theorem ext4_mul_add_mop_impl (A : Word) :
    ImplementsAtW A Code.ext4_mul_add_mop [] 16 mulAddPre 16 mulAddPost := by
  intro s hentry _ hcall hpre
  simp only [mulAddPre, argOk, disj16, RAM_END] at hpre
  obtain ⟨⟨ha4, hasp, haR⟩, ⟨hx4, hxsp, hxR⟩, ⟨hc4, hcsp, hcR⟩, hax, hac, -, -, -⟩ := hpre
  rw [Call, hentry] at hcall
  unfold ReturnsW
  rv_start Code.ext4_mul_add_mop hcall
  rv_steps 49 with hentry
  rv_ret
  refine ⟨by rv_regs, ?_, by rv_callee, by rv_frameW⟩
  simp only [mulAddPost, canon4, e4At]
  simp (disch := rv_disch) only [rv_state, read_write_same4, read_write_off, read_write_off0r]
  generalize read s.mem (s.getReg 10#5) 4 = a0 at *
  generalize read s.mem (s.getReg 10#5 + 4#32) 4 = a1 at *
  generalize read s.mem (s.getReg 10#5 + 8#32) 4 = a2 at *
  generalize read s.mem (s.getReg 10#5 + 12#32) 4 = a3 at *
  generalize read s.mem (s.getReg 11#5) 4 = b0 at *
  generalize read s.mem (s.getReg 11#5 + 4#32) 4 = b1 at *
  generalize read s.mem (s.getReg 11#5 + 8#32) 4 = b2 at *
  generalize read s.mem (s.getReg 11#5 + 12#32) 4 = b3 at *
  generalize read s.mem (s.getReg 12#5) 4 = c0 at *
  generalize read s.mem (s.getReg 12#5 + 4#32) 4 = c1 at *
  generalize read s.mem (s.getReg 12#5 + 8#32) 4 = c2 at *
  generalize read s.mem (s.getReg 12#5 + 12#32) 4 = c3 at *
  refine ⟨⟨mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun,
    mopVal_lt _ _ _ _ nofun⟩, ?_⟩
  simp only [e4, mont_add, mont_fma, mont_mul, mont_nonres, Spec.ofLimbs_mul, Spec.ofLimbs_add]
  congr 1 <;> ring
end RV
