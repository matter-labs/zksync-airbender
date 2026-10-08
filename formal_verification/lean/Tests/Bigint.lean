import Airbender.Review.Bigint.Theorems

namespace Tests.Bigint
open Airbender

/-- Simultaneous ADD and SUB requests cannot satisfy the imported row, regardless
    of operands or supplied fixed-table rows. The carry bit is not an opcode. -/
theorem twoOperationsRejected (setup : Table (ZMod babyBearModulus) (fields 3))
    (input register : Arithmetic.Word) (w : Nat → ZMod babyBearModulus) :
    let output : Bigint.Control.Output := ⟨register, #v[true, true, false, false, false, false, false, false]⟩
    ¬ (Bigint.Control.circuitModel setup).relation input output w := by
  intro output row
  have valid := Bigint.Control.babyBear_soundness setup input output w row
  have count := valid.2.2.1
  norm_num [Bigint.Control.operationCount, output, Fin.sum_univ_succ] at count

/-- Incoming control is a byte enforced by native equations, not a range premise. -/
theorem oversizedControlRejected (setup : Table (ZMod babyBearModulus) (fields 3))
    (input : Arithmetic.Word) (output : Bigint.Control.Output) (w : Nat → ZMod babyBearModulus)
    (oversized : 256 ≤ input.lo) :
    ¬ (Bigint.Control.circuitModel setup).relation input output w := by
  intro row
  have valid := Bigint.Control.babyBear_soundness setup input output w row
  have bound := valid.2.1
  omega

end Tests.Bigint
