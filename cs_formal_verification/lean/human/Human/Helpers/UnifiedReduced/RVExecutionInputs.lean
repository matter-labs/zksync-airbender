import Human.Helpers.UnifiedReduced.RVProgram
import Human.Circuits.UnifiedReduced.Tables.SetupRV
import Human.Helpers.Context.RVPooledBoundary

/-! RV siblings of `BootInputsWith`/`ExecutionInputsWith` (`NativeROM.lean`, `ExecutionInputs.lean`): the public
    starting state is an `RV.State`; its ROM image (`rom`) holds the program, and the trace's RAM seeds are the `Init`
    tokens of the unified machine's inline inits/teardowns sets, as `Trace.RVPooledBootInputs` takes them from the
    standalone circuit. Sail-only conditions are absent: the machine configuration (`Configured`), the Sail memory-map
    profile (`OrdinaryWordAddress`), the LW-to-x0 exclusion (a load into x0 is a no-op in `RV.exec`) and the
    code-domain guard (the RV table's fetch guard, `rvProgramEntryWith`). -/

namespace Airbender.UnifiedReduced
open Trace

/-- Public boot inputs: initial cells, public instruction bytes, clocks and the modeled setup table. Nothing here
    supplies an instruction's operands or result.

    Seeds: the registers are seeded by the chunk's public state (zero for the first chunk); the RAM is seeded by the
    `Init` tokens of `inits`, the inline inits/teardowns sets (`InitsTeardowns.unifiedLayout`) of the unified instances
    that carry them, whose public top bits pass the verifier's check (`TopBitsChecked`), so the tracked RAM is the union
    of their windows (`windowCells`, ROM shadow below 4 MiB included; the inline sets cover addresses below `2 ^ 31`).
    `image` ties the spec's starting state to those seeds; `BootRamZeroClaim` derives from it that every tracked RAM
    cell starts at 0.

    Link to the trace: only through the seeds. The `Init` tokens depend on the instances' public top bits alone (not on
    their columns), so no row-position view of `trace.rows` is needed here: `trace.rows` lists the active rows of all
    unified instances, unordered, while only the trailing instances carry inits/teardowns
    (`unified_circuit_statement.rs:105-110, 160-190`: leading instances report zero top bits and contribute none), and
    each `InitsTeardowns.Witness` carries its own instance's columns by row position, which only the teardown side
    reads. -/
structure RVBootInputs [Fact p.Prime] (trace : UnifiedTrace p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry)
    (inits : List (InitsTeardowns.Witness p InitsTeardowns.unifiedLayout)) : Prop where
  /-- Each tracked register or aligned RAM word occurs once. -/
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- The spec starts at PC 0. -/
  pc : initial.pc = 0
  /-- The spec's registers start at 0. -/
  registersZero : ∀ index, (Cell.register index).readRV initial = some 0
  /-- The full statement verifier's check of the instances' public top bits. -/
  topBits : InitsTeardowns.TopBitsChecked (inits.flatMap fun w => w.topBits.toList)
  /-- The native seeds: the register seeds, then the instances' `Init` tokens. -/
  seeds : trace.initialMemory = registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens
  /-- The tracked domain: the registers, then the instances' RAM windows. -/
  domain : cells = registerCells ++
    InitsTeardowns.windowCells InitsTeardowns.unifiedLayout (inits.flatMap fun w => w.topBits.toList)
  /-- Reading the tracked cells of the starting state gives the native seeds. -/
  image : initialImageRV initial cells = some trace.initialMemory
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
