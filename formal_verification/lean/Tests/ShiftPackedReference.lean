import Airbender.Proofs.Tables.ShiftPackedRows

namespace Tests.ShiftPackedReference
open Airbender.Verification.ShiftPackedReference
open Airbender.Setup.Proofs PackedSignedRun
set_option warningAsError true

theorem signed_fill : rowByte 0 3 128 251 = 255 := by decide +kernel
theorem unsigned_shift : rowByte 0 1 128 66 = 128 := by decide +kernel
theorem reverse_byte : rowByte 3 0 42 5 = 42 := by decide +kernel
theorem reverse_nonzero_amount : rowByte 3 0 42 13 = 0 := by decide +kernel
theorem invalid_control : rowByte 0 0 255 4 = 0 := by decide +kernel

theorem packed_signed_fill : digit 65536 (expectedRow 0 896) 251 = 255 := by decide +kernel

theorem packed_matches_reference (lane «start» count index : Nat) (laneBound : lane < 4)
    (inside : «start» + count ≤ 262144) (spanBound : «start» % 256 + count ≤ 4096)
    (within : index < count) :
    digit 65536 (expectedSpan lane «start» count) index =
      Airbender.Verification.ShiftCertificate.outputNatByte lane («start» + index) :=
  expectedSpan_digit lane «start» count index laneBound inside spanBound within

end Tests.ShiftPackedReference
