import Airbender.Proofs.ReducedMachine.SignHigh

namespace Airbender.ReducedMachine.SignHigh

/-- Exact native key, sign, high byte and tag for membership in the exported region. -/
theorem native_sign_high (query : Vector (ZMod mersenne31Modulus) 4)
    (member : Contains query) :
    query[0].val < 65536 ∧ query[1].val = query[0].val / 32768 ∧
      query[2].val = query[0].val / 256 ∧ query[3] = 16 :=
  SignHighProofs.result query member

end Airbender.ReducedMachine.SignHigh
