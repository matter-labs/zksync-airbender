import Human.Helpers.Delegation.MixedMemory
import Human.Helpers.Delegation.RVSharedMemory
import Human.Helpers.Decoder.RVPooledProgram

/-! RV siblings of the mixed ordinary/caller/worker pool records (`MixedMemory.lean`) over `RVRequestTrace`: both
    decoder tables are RV tables (`RV.decode` of the same public ROM image), the shared seeds are `initialImageRV`
    reads. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.Delegation.Caller
open Trace

/-- RV sibling of `RequestTrace.mixedSteps`: ordinary instructions, delegation callers and all worker transfers. -/
def RVRequestTrace.mixedSteps [Fact p.Prime] (data : RVRequestTrace p) :=
  data.machine.rows.flatMap (fun row => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++ data.workers.steps

/-- RV sibling of `MixedMemoryAccepted`: every noncaller row's decoder query is in the RV six-family table. -/
structure RVMixedMemoryAccepted [Fact p.Prime] (data : RVRequestTrace p)
    (program : List RVPooledProgramEntry) : Prop extends RVRequestChecks data where
  ordinaryDecoded : ∀ row ∈ data.machine.rows, row ∉ data.callers →
    (Trace.rvDecoderTable program row.family).Contains #[] row.decoderQuery
  memory : (data.machine.initialMemory ++ data.mixedSteps.map Prod.snd).Perm
    (data.machine.terminalMemory ++ data.mixedSteps.map Prod.fst)

/-- RV sibling of `MixedMemoryInputs`: public RV initialization (`initialImageRV`), both RV decoder tables from the
    same public ROM image, and the modeled setup. As in `RVPooledHistoryInputs`, the word-ROM table holds the ROM
    image's words at the public cells (`romImageRV`, the ROM image `rom`, not RAM) and the subword table the ROM
    image's words (`ROM.wordsRV`). -/
structure RVMixedMemoryInputs [Fact p.Prime] (data : RVRequestTrace p)
    (program : List RVPooledProgramEntry) (before : RV.State)
    (callerAddresses ordinaryAddresses : List (BitVec 32)) (cells : List Cell) : Prop
    extends RVSharedMemoryInputs data before callerAddresses cells where
  ordinaryProgram : rvProgramImageWith rvPooledDecoderFields before ordinaryAddresses = some program
  wordTable : data.machine.rom.wordMemory = ROM.table cells (romImageRV before cells)
  subwordTable : data.machine.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV before)
  tables : data.workers.setup = modeledSetup Keccak.Controller.rows
  rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round

end Airbender.Delegation.Caller
