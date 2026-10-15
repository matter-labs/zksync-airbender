import Airbender.Proofs.AddSub.ModularExternalComposition
import Airbender.Review.Helpers.Context.PaddingBoundary.Theorems

namespace Airbender.AddSub.Modular.External
open Trace
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- All six ordinary families, four modular operations and external reads/hints
    retire in one initialized history. Only reads consume the independent stream;
    operands, selectors, old destinations and terminal PC/cells are derived. -/
theorem soundness
    {trace : PooledTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry} {stream : List (BitVec 32)}
    (inputs : PooledInputs trace initial cells program decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program)
    (ports : StreamPorts trace stream) :
    Realizes stream program trace initial cells :=
  Proofs.trace_execution (by decide) (by decide) inputs accepted decoded ports

/-- Combined execution from native boot/ROM, with exact stream consumption. -/
theorem native_soundness
    {trace : PooledTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry} {stream : List (BitVec 32)}
    (inputs : PooledBootInputs trace initial cells program decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program)
    (ports : StreamPorts trace stream) :
    Realizes stream program trace initial cells (ROMView.token initial) :=
  Proofs.native_trace_execution (by decide) (by decide) inputs accepted decoded ports

/-- The existing external mask boundary removes only inactive contributions;
    stream ports and consumption refer to the derived architectural trace. -/
theorem padded_native_soundness
    {trace : PooledTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry} {stream : List (BitVec 32)}
    (inputs : PooledBootInputs (PaddingBoundary.active trace) initial cells program decoderFields)
    (accepted : PaddingBoundary.AcceptedLayout trace)
    (decoded : PooledDecoded (PaddingBoundary.active trace) program)
    (ports : StreamPorts (PaddingBoundary.active trace) stream) :
    Realizes stream program (PaddingBoundary.active trace) initial cells (ROMView.token initial) :=
  native_soundness (trace := PaddingBoundary.active trace) inputs
    (PaddingBoundary.acceptance_soundness accepted) decoded ports

end Airbender.AddSub.Modular.External
