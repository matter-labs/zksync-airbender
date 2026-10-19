import Airbender.Proofs.Tables.SllLow

namespace Airbender.Verification

theorem native_sll_low_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    sllLowTable.Contains #[] query ↔ NativeSllLow.Contains query :=
  SllLowProofs.native_membership query

theorem native_sll_low_result (query : Vector (ZMod mersenne31Modulus) 3)
    (member : NativeSllLow.Contains query) :
    query[0].val < 2097152 ∧ query[1].val < 65536 ∧ query[2].val < 65536 ∧
      BitVec.ofNat 32 (query[1].val + query[2].val * 65536) =
        (BitVec.ofNat 32 (query[0].val % 65536)) <<< (query[0].val / 65536) :=
  SllLowProofs.native_result query member

end Airbender.Verification
