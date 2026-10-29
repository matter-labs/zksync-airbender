import Airbender.Proofs.UnifiedReduced.SupportedUsePrefix
import Airbender.Proofs.UnifiedReduced.StreamCalls
import Airbender.Proofs.Trace.ExternalStream

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Trace
set_option warningAsError true

/-- Cutting a native stream trace preserves its public memory inputs. -/
def supported_prefix_inputs
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (point : PCState.State babyBearModulus)
    (memory : List (MemoryToken babyBearModulus)) :
    NativeMemoryInputsWith Stream.decoderFields
      (Caller.Proofs.supportedPrefix data point memory) program initial ca oa cells :=
  ⟨⟨inputs.publicProgram.image, inputs.publicProgram.initialClock,
      inputs.publicProgram.initialAligned⟩,
    inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables⟩

/-- The supported-use prefix retains the exact external response bindings. -/
theorem supported_prefix_stream_ports
    {data : RequestTrace babyBearModulus} {stream : List (BitVec 32)}
    (ports : Stream.StreamPorts data.machine stream)
    (point : PCState.State babyBearModulus)
    (memory : List (MemoryToken babyBearModulus)) :
    Stream.StreamPorts (Caller.Proofs.supportedPrefix data point memory).machine stream :=
  ExternalStream.Proofs.ports_before Trace.Row.clock Stream.isRead Stream.response
    data.machine.rows (timeOfPair point.timestamp).value ports

/-- The native prefix consumes exactly the words before the next instruction. -/
theorem supported_prefix_read_count (data : RequestTrace babyBearModulus)
    (next : Trace.Row babyBearModulus UnifiedFamily)
    (memory : List (MemoryToken babyBearModulus)) :
    Stream.readCount (Caller.Proofs.supportedPrefix data next.start memory).machine =
      ExternalStream.index Trace.Row.clock Stream.isRead data.machine.rows next :=
  ExternalStream.Proofs.count_before Trace.Row.clock Stream.isRead data.machine.rows next

end Airbender.UnifiedReduced.Caller.Stream.Proofs
