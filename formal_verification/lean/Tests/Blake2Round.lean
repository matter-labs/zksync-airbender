import Airbender.Review.Blake2Round.Theorems

namespace Tests.Blake2Round
open Airbender

/-- A row whose next round mask does not shift is rejected by the imported
    assertions, independently of which XOR setup is supplied. -/
theorem wrongControlRejected (setup : Table (ZMod babyBearModulus) (fields 4))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (Blake2Round.Control.circuitModel setup).relation ⟨123, 8⟩ ⟨0, 8⟩ w := by
  intro row
  have correct := Blake2Round.Control.babyBear_soundness setup ⟨123, 8⟩ ⟨0, 8⟩ w row
  have high := congrArg Arithmetic.Word.hi correct.2
  norm_num [Blake2Round.Control.next] at high

end Tests.Blake2Round
