import Airbender.Proofs.Tables.Binary

namespace Airbender.Verification

/-- Clean binary membership is exactly actual native tagged row membership. -/
theorem native_binary_membership (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    (binaryTable kind).Contains #[] query ↔ NativeBinary.Contains kind query :=
  BinaryProofs.native_membership kind query

/-- Actual native XOR/OR/AND rows bound both byte keys and force the bitwise result. -/
theorem native_binary_result (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 3)
    (member : NativeBinary.Contains kind query) :
    query[0].val < 256 ∧ query[1].val < 256 ∧ query[2].val < 256 ∧
      BitVec.ofNat 8 query[2].val = byteOperation kind.tag
        (BitVec.ofNat 8 query[0].val) (BitVec.ofNat 8 query[1].val) :=
  BinaryProofs.native_result kind query member

end Airbender.Verification
