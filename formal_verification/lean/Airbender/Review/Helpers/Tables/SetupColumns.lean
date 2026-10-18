import Airbender.Review.Helpers.Core.Word

namespace Airbender.Verification

/-- Physical v2 setup placement imported from the compiled layout. Generic
    groups have three values plus a tag; decoder groups have ten columns.
    The final trace row is reserved for normalization, not lookup membership. -/
structure SetupColumns where
  traceLength : Nat
  width : Nat
  range16 : Nat
  timestamp19 : Nat
  genericStart : Nat
  genericGroups : Nat
  decoderStart : Nat
  decoderCapacity : Nat
  genericRows : Nat
  deriving DecidableEq

end Airbender.Verification
