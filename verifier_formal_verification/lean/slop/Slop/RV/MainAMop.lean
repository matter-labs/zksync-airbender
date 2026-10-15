import Slop.RV.MainA
import Slop.RV.InitMop
import Slop.RV.Code.main_mop

/-! The first part of `main` in the `mop` image. -/

namespace RV
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- From `main`'s entry: `init`, the inputs, `combine` and `poly_eval`; up to `main + 0x6c`. -/
theorem main_a_mop (S : State) (x y0 y1 y2 y3 : Word) (hpc : S.pc = 0x38#32) (h2 : S.getReg 2#5 = 0x13ffff0#32)
    (hra : (S.getReg 1#5).toNat % 4 = 0)
    (hmain : CodeAt S 0x38#32 Code.main_mop) (hinit : CodeAt S 0x644#32 Code.init_mop)
    (hmc : CodeAt S 0x6cc#32 Code.memcpy) (hcomb : CodeAt S 0x410#32 Code.combine)
    (hinc : CodeAt S 0x47c#32 Code.inc) (hdbl : CodeAt S 0x458#32 Code.double)
    (hpoly : CodeAt S 0x394#32 Code.poly_eval) (hmul : CodeAt S 0x358#32 Code.mul_mod)
    (hadd : CodeAt S 0x324#32 Code.add_mod) (hcoef : CodeAt S 0x20fc#32 Code.COEFFS)
    (hcoef4 : CodeAt S (0x20fc#32 + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hx : read S.mem 0x1401000#32 4 = x) (hy0 : read S.mem 0x1401004#32 4 = y0)
    (hy1 : read S.mem 0x1401008#32 4 = y1) (hy2 : read S.mem 0x140100c#32 4 = y2)
    (hy3 : read S.mem 0x1401010#32 4 = y3) (hxP : x.toNat ≤ P) :
    ∃ m T, run m S = some T ∧ T.pc = 0xa4#32 ∧ T.getReg 2#5 = 0x13fffa0#32 ∧ T.getReg 18#5 = 3#32 * x + 1#32 ∧
      (T.getReg 9#5).toNat ≤ P ∧ (T.getReg 9#5).toNat % P = polyW Code.COEFFS x.toNat % P ∧
      T.getReg 19#5 = y3 ∧ T.getReg 20#5 = y2 ∧ T.getReg 21#5 = y1 ∧ T.getReg 22#5 = y0 ∧
      CodeMem T.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4 ∧
      (∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b) := by
  main_a_proof Code.main_mop init_run_mop (0x644#32) (0x410#32) (0x394#32) (0x20fc#32)

end RV
