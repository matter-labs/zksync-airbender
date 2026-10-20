import Slop.Sym.Meta
import Slop.RV.Code.merkle_check

/-! The symbolic runs of `merkle_check`'s end (for `RV/Merkle/Exit.lean`): the comparison of the computed node with the
root (words 68 … 93, up to the branch at 94), and the epilogue (words 95 … 108, up to `ret` at 109). -/

namespace RV
open RV.Sym
set_option maxHeartbeats 400000

sym_run MCmp := (Code.merkle_check.drop 68).take 26
sym_run MEpi := (Code.merkle_check.drop 95).take 14

/-- The computed node (`a0` after word 93, node 54) is zero iff the eight words at `s10 + 256` equal the root
registers `s9 … s2` (x25, x24, x23, x22, x20, x21, x19, x18). -/
theorem exit_cmp (c : Ctx) : MCmp.σ.pool.val c 54 = 0#32 ↔
    (c.env 25 = read c.m (c.env 26 + 256#32) 4 ∧ c.env 24 = read c.m (c.env 26 + 260#32) 4 ∧
     c.env 23 = read c.m (c.env 26 + 264#32) 4 ∧ c.env 22 = read c.m (c.env 26 + 268#32) 4 ∧
     c.env 20 = read c.m (c.env 26 + 272#32) 4 ∧ c.env 21 = read c.m (c.env 26 + 276#32) 4 ∧
     c.env 19 = read c.m (c.env 26 + 280#32) 4 ∧ c.env 18 = read c.m (c.env 26 + 284#32) 4) := by
  sym_unfold
  simp only [sext_word, ite_true, alu, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, and_assoc]

end RV
