import Airbender.Proofs.Tables.SrlHigh

namespace Airbender.Verification

theorem native_srl_high_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    srlHighTable.Contains #[] query ↔ NativeSrlHigh.Contains query :=
  SrlHighProofs.native_membership query

theorem native_srl_high_result (query : Vector (ZMod mersenne31Modulus) 3)
    (member : NativeSrlHigh.Contains query) :
    query[0].val < 2097152 ∧ query[1].val < 65536 ∧ query[2].val < 65536 ∧
      BitVec.ofNat 32 (query[1].val + query[2].val * 65536) =
        (BitVec.ofNat 32 ((query[0].val % 65536) * 65536)) >>> (query[0].val / 65536) :=
  SrlHighProofs.native_result query member

end Airbender.Verification
