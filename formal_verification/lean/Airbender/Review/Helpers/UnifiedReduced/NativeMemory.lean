import Airbender.Review.Helpers.UnifiedReduced.MixedMemory

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Public memory/program boundary for native-enforced calls. No occurrence
plan, controller dataflow, round-mask selection, or desired result is supplied. -/
structure NativeMemoryInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (before : Reference.RiscV.Sail.State)
    (callerAddresses ordinaryAddresses : List (BitVec 32)) (cells : List Cell) : Prop where
  publicProgram : RequestInputs data before callerAddresses
  ordinaryProgram : Mixed.programImage before ordinaryAddresses = some program
  initialization : initialImage before cells = some data.machine.initialMemory
  distinct : (cells.map Cell.addressCode).Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  setup : data.machine.rom = Setup.table before
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows

/-- Compatibility with the existing initialized boundary; its extra mask
premise is discarded, rather than retained by the native execution entrypoint. -/
def MixedMemoryInputs.toNative [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (inputs : MixedMemoryInputs data program before ca oa cells) :
    NativeMemoryInputs data program before ca oa cells :=
  ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization,
    inputs.distinct, inputs.aligned, inputs.setup, inputs.tables⟩

end Airbender.UnifiedReduced.Caller
