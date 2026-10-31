import Airbender.Data.Decoder.SelectedProgram
import Airbender.Review.Compiler.Pooled
import Airbender.Review.Compiler.Unified
import Airbender.Review.Helpers.Decoder.PooledExternalInput
import Airbender.Review.Helpers.UnifiedReduced.ExecutionInputs

namespace Airbender.Compiler
open Airbender Airbender.Trace Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public execution inputs for an independently supplied pooled program, and
the structural interpretation of this retained capture's decoder table.
The equality is independent of trace rows and supplies no query membership.
These captures support compatible decoder tables; a different compiled setup
requires its own table interpretation proof. -/
structure PooledExecution.ProgramBoundary (trace : PooledTrace babyBearModulus)
    (before : State) (cells : List Cell) (program : List PooledProgramEntry) : Prop where
  execution : PooledBootInputs trace before cells program NonDeterminism.Pooled.decoderFields
  image : ROM.ImportedImage before
  domain : ROMNative.WordFullPublic.CoversROM cells
  decoderTables : ∀ family,
    decoderTable (p := babyBearModulus) Airbender.Trace.NativeDecoder.pooledProgram family =
      decoderTable program family

/-- Public execution inputs and a trace-independent structural decoder-table
interpretation for a supplied unified program. The retained setup instance is
still fixed; arbitrary new setups require new interpretation evidence. -/
structure UnifiedExecution.ProgramBoundary (trace : UnifiedTrace babyBearModulus)
    (before : State) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry) : Prop where
  execution : UnifiedReduced.ExecutionInputs trace before cells program
  image : ROM.ImportedImage before
  decoderTables : ∀ family,
    decoderTable (p := babyBearModulus) Airbender.Trace.NativeDecoder.unifiedProgram family =
      decoderTable program family

end Airbender.Compiler
