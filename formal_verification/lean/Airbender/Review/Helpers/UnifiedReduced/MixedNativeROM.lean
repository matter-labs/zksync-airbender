import Airbender.Review.Helpers.UnifiedReduced.MixedMemory
import Airbender.Review.Helpers.UnifiedReduced.NativeROM
import Airbender.Review.Helpers.Context.ExternalBoundary.WorkerRAM

namespace Airbender.UnifiedReduced.Caller.NativeROM
open Trace Reference.RiscV.Sail

/-- Interpret the actual unified ROM slots using public bytes. Workers and
    full-width caller requests retain their original assignments and setup. -/
def view [Fact p.Prime] (initial : State) (native : RequestTrace p) : RequestTrace p :=
  { native with machine := UnifiedReduced.ROMView.data initial native.machine }

/-- Public native boot image, original ordinary/caller decoding and modeled
    worker tables. The RAM-port contract is a separate lower-level RAM-domain premise;
    these inputs supply no row reads, worker results or physical history. -/
structure Inputs [Fact p.Prime] (native : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (initial : State) (cells : List Cell) : Prop where
  machine : BootInputsWith Mixed.decoderFields native.machine initial cells program
  callers : ∃ addresses, programImage initial addresses = some native.program
  tables : native.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  rounds : ∀ row ∈ native.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round

end Airbender.UnifiedReduced.Caller.NativeROM
