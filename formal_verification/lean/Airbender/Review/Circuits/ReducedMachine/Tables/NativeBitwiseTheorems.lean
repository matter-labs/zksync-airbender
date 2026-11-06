import Airbender.Proofs.ReducedMachine.NativeBitwiseTable

namespace Airbender.ReducedMachine.NativeFixed
open Verification
set_option autoImplicit false

/-- Actual full-pool byte relation at its native tag, including exact arithmetic
    and all key/output bounds. No region/equivalence premise is supplied. -/
theorem bitwise_implementation (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (kind.tag : ZMod mersenne31Modulus)) :
    query[0].val < 256 ∧ query[1].val < 256 ∧ query[2].val < 256 ∧
      BitVec.ofNat 8 query[2].val = byteOperation kind.tag
        (BitVec.ofNat 8 query[0].val) (BitVec.ofNat 8 query[1].val) :=
  NativeBitwiseTableProofs.result kind query member selected

end Airbender.ReducedMachine.NativeFixed
