import Airbender.Proofs.AddSub.ModularComposition
import Airbender.Review.Helpers.Context.PaddingBoundary.Theorems

namespace Airbender.AddSub.Modular.Pooled
open Trace
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Whole six-family execution including all four modular operations. Public
    bytes determine decoding; initialized matching derives operands, selectors,
    FMAMOD's old destination and terminal PC/cells. Modular arithmetic uses the
    pinned project specification in BabyBear. -/
theorem soundness
    {trace : PooledTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledInputs trace initial cells program decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (Step program) trace initial cells :=
  Proofs.trace_execution (by decide) (by decide) inputs accepted decoded

/-- The same execution from native boot and zero ROM shadows, interpreted
    against public bytes through the existing ROM view. -/
theorem native_soundness
    {trace : PooledTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace initial cells program decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (Step program) trace initial cells (ROMView.token initial) :=
  Proofs.native_trace_execution inputs accepted decoded

/-- External masked closure erases inactive rows before the same native
    execution proof. Raw constraints and all existing public boundaries remain. -/
theorem padded_native_soundness
    {trace : PooledTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs (PaddingBoundary.active trace) initial cells program decoderFields)
    (accepted : PaddingBoundary.AcceptedLayout trace)
    (decoded : PooledDecoded (PaddingBoundary.active trace) program) :
    Realizes (Step program) trace initial cells (ROMView.token initial) :=
  native_soundness (trace := PaddingBoundary.active trace) inputs
    (PaddingBoundary.acceptance_soundness accepted) decoded

end Airbender.AddSub.Modular.Pooled
