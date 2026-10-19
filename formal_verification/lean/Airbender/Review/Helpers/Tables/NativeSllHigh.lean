import Airbender.Proofs.Tables.SllHigh

namespace Airbender.Verification

theorem native_sll_high_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    sllHighTable.Contains #[] query ↔ NativeSllHigh.Contains query :=
  SllHighProofs.native_membership query

theorem native_sll_high_result (query : Vector (ZMod mersenne31Modulus) 3)
    (member : NativeSllHigh.Contains query) :
    query[0].val < 2097152 ∧ query[2].val < 65536 ∧ query[1] = 0 ∧
      BitVec.ofNat 32 (query[2].val * 65536) =
        (BitVec.ofNat 32 ((query[0].val % 65536) * 65536)) <<< (query[0].val / 65536) :=
  SllHighProofs.native_result query member

end Airbender.Verification
