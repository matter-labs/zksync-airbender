import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Arithmetic.FieldChunks
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

open Arithmetic Blake2G.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Two native chunk XORs imply XOR of the canonical sixteen-bit limbs. -/
theorem xor_limb_chunks {p width remaining : Nat} [Fact p.Prime]
    (hp : 65536 ≤ p) (capacity : 2 ^ width * 2 ^ remaining = 65536)
    {x y z xl xh yl yh zl zh : ZMod p}
    (low : chunkXor width xl yl zl) (high : chunkXor remaining xh yh zh)
    (xChunks : x = xl + (2 ^ width : Nat) * xh)
    (yChunks : y = yl + (2 ^ width : Nat) * yh)
    (zChunks : z = zl + (2 ^ width : Nat) * zh) :
    x.val < 65536 ∧ y.val < 65536 ∧ z.val < 65536 ∧ z.val = x.val ^^^ y.val := by
  have bound : 2 ^ width * 2 ^ remaining ≤ p := by rw [capacity]; exact hp
  have xv := value_of_chunks bound low.1 high.1 xChunks
  have yv := value_of_chunks bound low.2.1 high.2.1 yChunks
  have zv := value_of_chunks bound low.2.2.1 high.2.2.1 zChunks
  have small {a b : Nat} (ha : a < 2 ^ width) (hb : b < 2 ^ remaining) :
      a + 2 ^ width * b < 65536 := by
    calc
      _ < 2 ^ width + 2 ^ width * b := Nat.add_lt_add_right ha _
      _ = 2 ^ width * (b + 1) := by ring
      _ ≤ 2 ^ width * 2 ^ remaining := Nat.mul_le_mul_left _ (by omega)
      _ = _ := capacity
  refine ⟨xv ▸ small low.1 high.1, yv ▸ small low.2.1 high.2.1,
    zv ▸ small low.2.2.1 high.2.2.1, ?_⟩
  rw [xv, yv, zv, xor_of_chunks low.1 low.2.1, low.2.2.2, high.2.2.2]

end Airbender.Blake2Round.Proofs
