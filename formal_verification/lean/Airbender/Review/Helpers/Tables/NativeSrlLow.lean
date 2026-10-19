import Airbender.Proofs.Tables.SrlLow

namespace Airbender.Verification

theorem native_srl_low_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    srlLowTable.Contains #[] query ↔ NativeSrlLow.Contains query :=
  SrlLowProofs.native_membership query

theorem native_srl_low_result (query : Vector (ZMod mersenne31Modulus) 3)
    (member : NativeSrlLow.Contains query) :
    query[0].val < 2097152 ∧ query[1].val < 65536 ∧ query[2] = 0 ∧
      BitVec.ofNat 32 query[1].val =
        (BitVec.ofNat 32 (query[0].val % 65536)) >>> (query[0].val / 65536) :=
  SrlLowProofs.native_result query member

end Airbender.Verification
