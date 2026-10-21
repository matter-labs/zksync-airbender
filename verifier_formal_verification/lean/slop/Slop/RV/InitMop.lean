import Slop.RV.Init
import Slop.RV.Code.init_mop

/-! `init` of the `mop` image (`.rodata` at ROM `0x26d8`). -/

namespace RV

/-- `init_run` for the `mop` image. -/
theorem init_run_mop (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 136 + 4 * 1676 ≤ 4194304) (S : State)
    (hcode : CodeAt S A Code.init_mop) (hmc : CodeAt S (A + 136#32) Code.memcpy) (hpc : S.pc = A)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 32 ≤ (S.getReg 2#5).toNat)
    (hsp2 : (S.getReg 2#5).toNat ≤ 20971520) (hra : (S.getReg 1#5).toNat % 4 = 0) :
    ∃ m S', run m S = some S' ∧ S'.pc = S.getReg 1#5 ∧
      (∀ a : Word, a.toNat + 32 < (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ a.toNat →
        S'.mem a = blockCopy S.mem 20971520#32 9944#32 912 a) ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧
      (∀ i : Reg, i ≠ 10#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 → S'.getReg i = S.getReg i) :=
  init_run_of 0x000025b7#32 0x6d858593#32 0x000045b7#32 0x00002000#32 0x6d8#32 9944#32 16384#32 rfl rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) A hA hAr S hcode hmc hpc hsp hsp1 hsp2 hra

end RV
