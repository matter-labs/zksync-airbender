import Airbender.Review.Helpers.Delegation.MixedMemory
import Airbender.Review.Helpers.Decoder.ModularExternal

namespace Airbender.Delegation.Caller
open Trace

/-- Public memory inputs for pooled ordinary, modular, external and caller rows.
The worker controller contracts remain separate from this interface. -/
structure StreamMemoryInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List PooledProgramEntry) (initial : Reference.RiscV.Sail.State)
    (callerAddresses ordinaryAddresses : List (BitVec 32)) (cells : List Cell) : Prop
    extends SharedMemoryInputs data initial callerAddresses cells where
  ordinaryProgram : AddSub.Modular.External.programImage initial ordinaryAddresses = some program
  wordTable : data.machine.rom.wordMemory = ROM.table cells data.machine.initialMemory
  subwordTable : data.machine.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  tables : data.workers.setup = modeledSetup Keccak.Controller.rows

end Airbender.Delegation.Caller
