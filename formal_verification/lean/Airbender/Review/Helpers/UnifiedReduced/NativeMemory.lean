import Airbender.Review.Helpers.UnifiedReduced.MixedMemory
import Airbender.Review.Helpers.Context.ExternalBoundary.HashABI

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Public memory/program boundary. Hash controller validity and G base
separation are supplied separately by `HashCommands`, not derived here. -/
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

/-- Temporary hash input contracts for every actual worker. These are explicit
assumptions pending owner-reviewed circuit/VM resolution. They supply controller
membership and G pointer separation, never outputs or reference execution.
They do not assert that workers form complete hash protocols. -/
structure HashCommands [Fact p.Prime] (data : RequestTrace p) : Prop where
  gControl : ∀ w, ⟨.blakeG, w⟩ ∈ data.workers.rows → ExternalBoundary.HashABI.GControl w
  gBases : ∀ w, ⟨.blakeG, w⟩ ∈ data.workers.rows → ExternalBoundary.HashABI.GBases w
  roundControl : ∀ w, ⟨.blakeRound, w⟩ ∈ data.workers.rows → ExternalBoundary.HashABI.RoundControl w
  keccakControl : ∀ w, ⟨.keccak, w⟩ ∈ data.workers.rows → ExternalBoundary.HashABI.KeccakControl w

/-- Compatibility with the existing initialized memory boundary. This adapter
does not supply the separate `HashCommands` contract. -/
def MixedMemoryInputs.toNative [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (inputs : MixedMemoryInputs data program before ca oa cells) :
    NativeMemoryInputs data program before ca oa cells :=
  ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization,
    inputs.distinct, inputs.aligned, inputs.setup, inputs.tables⟩

end Airbender.UnifiedReduced.Caller
