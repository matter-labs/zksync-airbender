import Airbender.Proofs.Tables.NativeScalars

namespace Airbender.Verification.NativeSetup

/-- Actual exported scalar prefixes with source-shaped active zero padding
    recover the native 16/19-bit ranges. The reserved normalization row and
    Rust physical trace/LDE/argument refinement remain separate. -/
theorem native_scalar_lookup (kind : ScalarKind) (value : ZMod mersenne31Modulus) :
    ScalarContains kind value ↔ value.val < 2 ^ kind.bits :=
  Proofs.scalar_lookup kind value

end Airbender.Verification.NativeSetup
