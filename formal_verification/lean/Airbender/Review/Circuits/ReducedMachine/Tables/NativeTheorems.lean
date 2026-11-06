import Airbender.Proofs.ReducedMachine.NativePool

namespace Airbender.ReducedMachine.NativeFixed

/-- A native tag-16 query in the complete pool derives both exact outputs. -/
theorem sign_high (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 16) :
    query[0].val < 65536 ∧ query[1].val = query[0].val / 32768 ∧
      query[2].val = query[0].val / 256 ∧ query[3] = 16 :=
  SignHigh.native_sign_high query (NativePoolProofs.sign_member query member selected)

end Airbender.ReducedMachine.NativeFixed
