import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Helpers.Decoder.SelectedProgram
import Airbender.Proofs.Trace.ImportedDecoder

namespace Airbender.Trace

/-- Actual complete selected-program decoder setup supplies pooled decoding.
    The existing public boot, ROM, platform, verifier and logical matching
    boundaries are retained. Incoming PC-low typing follows from constraints
    and state matching; no table-content equivalence is a premise. -/
theorem pooled_imported_decoder_soundness
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : PooledTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell}
    (inputs : PooledBootInputs trace before cells NativeDecoder.pooledProgram)
    (accepted : Accepted trace) (decoded : NativeDecoder.PooledLookups trace) :
    Realizes (PooledStep NativeDecoder.pooledProgram) trace before cells
      (ROMView.token before) := by
  exact Proofs.pooled_imported_decoder_soundness inputs accepted decoded

end Airbender.Trace

namespace Airbender.UnifiedReduced

/-- Actual selected unified decoder rows, unsupported slots and the committed
    tail replace the modeled decoder-membership premise. Generalized programs
    keep their original claims; this entry explicitly selects the imported text. -/
theorem imported_decoder_execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell}
    (inputs : ImportedExecutionInputs trace initial cells Trace.NativeDecoder.unifiedProgram)
    (accepted : Trace.Accepted trace) (decoded : Trace.NativeDecoder.UnifiedLookups trace) :
    Trace.Realizes (Step Trace.NativeDecoder.unifiedProgram) trace initial cells
      (Trace.ROMView.token initial) := by
  exact Proofs.imported_decoder_execution_soundness hp clockInverse byteInverse inputs accepted decoded

end Airbender.UnifiedReduced
