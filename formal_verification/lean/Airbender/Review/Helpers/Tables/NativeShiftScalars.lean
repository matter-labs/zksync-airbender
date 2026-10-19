import Airbender.Proofs.Tables.ShiftScalars

namespace Airbender.Verification

theorem native_shift_scalar_membership (kind : ShiftScalarKind)
    (query : Vector (ZMod mersenne31Modulus) 3) :
    kind.table.Contains #[] query ↔ NativeShiftScalars.Contains kind query :=
  ShiftScalarProofs.native_membership kind query

theorem native_shift_truncation (query : Vector (ZMod mersenne31Modulus) 3)
    (member : NativeShiftScalars.Contains .truncate query) :
    query[0].val < 65536 ∧ query[1].val = query[0].val % 32 ∧ query[2] = 0 :=
  ShiftScalarProofs.truncate_result query member

theorem native_shift_padded_range (query : Vector (ZMod mersenne31Modulus) 3)
    (member : NativeShiftScalars.Contains .range query) :
    query[0].val < 65536 ∧ query[1] = 0 ∧ query[2] = 0 :=
  ShiftScalarProofs.range_result query member

theorem native_shift_sign_fill (query : Vector (ZMod mersenne31Modulus) 3)
    (member : NativeShiftScalars.Contains .signFill query) :
    query[0].val < 2097152 ∧ query[1].val < 65536 ∧ query[2].val < 65536 ∧
      BitVec.ofNat 32 (query[1].val + 65536 * query[2].val) =
        if query[0].val % 65536 < 32768 then (0 : BitVec 32)
        else (BitVec.allOnes 32) <<< (32 - query[0].val / 65536) :=
  ShiftScalarProofs.sign_result query member

end Airbender.Verification
