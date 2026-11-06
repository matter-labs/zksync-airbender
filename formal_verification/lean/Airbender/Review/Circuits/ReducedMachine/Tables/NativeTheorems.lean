import Airbender.Proofs.ReducedMachine.NativeTruncation
import Airbender.Proofs.ReducedMachine.NativeSignFill

namespace Airbender.ReducedMachine.NativeFixed

/-- A native tag-16 query in the complete pool derives both exact outputs. -/
theorem sign_high (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 16) :
    query[0].val < 65536 ∧ query[1].val = query[0].val / 32768 ∧
      query[2].val = query[0].val / 256 ∧ query[3] = 16 :=
  SignHigh.native_sign_high query (NativePoolProofs.sign_member query member selected)

/-- A tag-47 query in the actual complete native pool truncates to five bits. -/
theorem truncate_shift (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 47) :
    query[0].val < 65536 ∧ query[1].val = query[0].val % 32 ∧ query[2] = 0 :=
  NativeTruncationProofs.result query member selected

/-- Actual tag-20 membership fixes both bounded sign-fill output limbs. -/
theorem sign_fill (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 20) :
    query[0].val < 128 ∧ query[1].val = (signFillOutputs query[0].val)[0] ∧
      query[2].val = (signFillOutputs query[0].val)[1] ∧
      query[1].val < 65536 ∧ query[2].val < 65536 :=
  NativeSignFillProofs.result query member selected

end Airbender.ReducedMachine.NativeFixed
