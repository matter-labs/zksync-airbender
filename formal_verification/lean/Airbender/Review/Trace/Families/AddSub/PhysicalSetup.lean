import Airbender.Proofs.Trace.PhysicalSetup
import Airbender.Review.Trace.Families.AddSub.ActiveSetup

namespace Airbender.Trace

/-- Complete setup-row decoder lookups at actual compiled columns supply
    initialized original Sail execution. Logical state/memory matching remains
    explicit; Rust normalization/LDE and cryptographic enforcement are separate. -/
theorem physical_setup_sail_execution {trace : Data mersenne31Modulus}
    {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace initial cells)
    (image : AddSub.sparseDecoderSetupImage initial 7 20 = some AddSub.NativeSetup.setup)
    (accepted : Accepted trace)
    (decoded : ∀ row ∈ trace.rows,
      Verification.NativeSetup.ColumnLookup .arithmetic ⟨[], by decide⟩
        Verification.NativeSetup.DecoderKind.arithmetic.columns.decoderStart row.decoderQuery)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (SailStep AddSub.NativeSetup.setup.program) trace initial cells :=
  active_setup_sail_execution inputs image accepted (Proofs.physical_arithmetic_decoded decoded) aligned

end Airbender.Trace
