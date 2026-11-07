import Human.Helpers.UnifiedReduced.RVProgram
import Human.Circuits.UnifiedReduced.Tables.SetupRV
import Human.Helpers.Memory.InitialImageRV
import Human.Helpers.Memory.Native

/-! RV siblings of `BootInputsWith`/`ExecutionInputsWith` (`NativeROM.lean`, `ExecutionInputs.lean`): the public
    starting state is an `RV.State`; its ROM image (`rom`) holds the program and its RAM (`mem`, shadow RAM below
    `ROM_END` included) starts at zero, as the native seed. Sail-only conditions are absent: the machine configuration (`Configured`), the
    Sail memory-map profile (`OrdinaryWordAddress`), the LW-to-x0 exclusion (a load into x0 is a no-op in `RV.exec`)
    and the code-domain guard (the RV table's fetch guard, `rvProgramEntryWith`). -/

namespace Airbender.UnifiedReduced
open Trace

/-- Public boot inputs: initial cells, public instruction bytes, clocks and the modeled setup table. Nothing here
    supplies an instruction's operands or result. -/
structure RVBootInputs [Fact p.Prime] (trace : UnifiedTrace p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop where
  /-- Each tracked register or aligned RAM word occurs once. -/
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Initial PC zero, registers zero, all of RAM zero (shadow RAM included); the ROM image holds the program. -/
  profile : RVInitialProfile initial cells
  /-- Every tracked cell is readable in the starting state. -/
  image : ∃ image : List (MemoryToken p), initialImageRV initial cells = some image
  /-- Native seed values are zero (the starting RAM and registers). -/
  seed : trace.initialMemory = Trace.ROMView.nativeBootImage cells
  /-- Public starting PC zero and native timestamp four. Later clocks are proved. -/
  initialPC : trace.initial = PCState.boundary 0 (4, 0)
  /-- Public ROM bytes (`RV.read` of `rom`) and `RV.decode` construct the program table. -/
  programImage : ∃ addresses, rvProgramImageWith rvDecoderFields initial addresses = some program
  /-- The modeled setup table is fixed by the ROM image (`ROM.wordsRV`). -/
  setup : trace.rom = Setup.tableRV initial

/-- Public inputs of the unified execution claim: the boot inputs. Sail's register-domain condition is not needed: x0 and
    every other register a row reads are tracked cells through the row's own history. -/
abbrev RVExecutionInputs {p : Nat} [Fact p.Prime] := RVBootInputs (p := p)

end Airbender.UnifiedReduced
