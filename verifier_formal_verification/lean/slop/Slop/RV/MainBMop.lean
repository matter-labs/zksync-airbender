import Slop.RV.MainB
import Slop.RV.Code.main_mop

/-! The second part of `main` in the `mop` image. -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- From `main + 0x6c` (after `poly_eval`): the inputs `y` to the stack, `ext4_poly` (any implementation of its
contract), the 8 output words to `zksync_os_finish_success`, which ends at its final self-jump with the outputs in
`x10 … x25`. -/
theorem main_b_mop (T : State) (c p y0 y1 y2 y3 : Word) (codeEP : List Word)
    (calleesEP : List (Word × List Word)) (FEP : Nat)
    (hEP : ImplementsAtW 0x264#32 codeEP calleesEP FEP e4polyPre 16 e4polyPost)
    (hEPr : 0x264 + 4 * codeEP.length ≤ 4194304) (hFEP : FEP ≤ 0x100000)
    (hcalr : ∀ c ∈ calleesEP, c.1.toNat + 4 * c.2.length ≤ 4194304)
    (hpc : T.pc = 0xa4#32) (h2 : T.getReg 2#5 = 0x13fffa0#32) (h18 : T.getReg 18#5 = c) (h9 : T.getReg 9#5 = p)
    (h19 : T.getReg 19#5 = y3) (h20 : T.getReg 20#5 = y2) (h21 : T.getReg 21#5 = y1) (h22 : T.getReg 22#5 = y0)
    (htab : CodeMem T.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hmain : CodeAt T 0x38#32 Code.main_mop) (hEPc : CodeAt T 0x264#32 codeEP) (hcal : ∀ c ∈ calleesEP, CodeAt T c.1 c.2)
    (hfin : CodeAt T 0x548#32 Code.finish_success) (hext : CodeAt T 0x5c0#32 Code.finish_success_extended)
    (hy0 : y0.toNat < BabyBearP) (hy1 : y1.toNat < BabyBearP) (hy2 : y2.toNat < BabyBearP)
    (hy3 : y3.toNat < BabyBearP) :
    ∃ m W, run m T = some W ∧ W.pc = 0x640#32 ∧ W.getReg 10#5 = c ∧ W.getReg 11#5 = p ∧
      (∀ i : Reg, 12 ≤ i.toNat → i.toNat ≤ 15 → (W.getReg i).toNat < BabyBearP) ∧
      ofLimbs ((W.getReg 12#5).toNat : F) ((W.getReg 13#5).toNat : F) ((W.getReg 14#5).toNat : F)
        ((W.getReg 15#5).toNat : F) = poly4 (ofLimbs (y0.toNat : F) (y1.toNat : F) (y2.toNat : F) (y3.toNat : F)) ∧
      (∀ i : Reg, 16 ≤ i.toNat → i.toNat ≤ 25 → W.getReg i = 0) ∧
      (∀ b : Word, b.toNat < ROM_END → W.mem b = T.mem b) := by
  main_b_proof Code.main_mop (0x548#32) (0x5c0#32)

end RV
