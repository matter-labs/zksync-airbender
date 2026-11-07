import Human.Helpers.Context.RVInterfaces
import Human.Helpers.Memory.Native
import Human.Circuits.InitsTeardowns.Theorems

/-! RV sibling of `PooledBootInputs` (`PooledBoundary.lean`): the public starting state is an `RV.State`, and the
    trace's RAM seeds are the inits/teardowns circuit's `Init` tokens (`InitsTeardowns.Witness.initTokens`) instead of
    an assumed zero image. -/

namespace Airbender.Trace

/-- The 32 register cells, x0 first. -/
def registerCells : List Cell := (List.range 32).map fun index => .register (BitVec.ofNat 5 index)

/-- The register seeds: zero value and timestamp for each register cell. -/
def registerSeeds {p : Nat} : List (MemoryToken p) := ROMView.nativeBootImage registerCells

/-- Public boot inputs of the six-family claims over our spec. Sail-only conditions of `PooledBootInputs` are absent:
    the machine configuration (`configuration`), the Sail memory-map profile (`ordinary`), the LW-to-x0 exclusion
    (`loads`: a load into x0 is a no-op in `RV.exec`) and the code-domain guard (`code`: the RV table's fetch guard).

    Seeds: the registers are seeded by the chunk's public state (zero for the first chunk), not by the inits/teardowns
    circuit; the RAM is seeded by the `Init` tokens of the inits/teardowns instances `inits`, whose public top bits pass
    the verifier's check (`TopBitsChecked`), so the tracked RAM is the union of their windows (`windowCells`, ROM shadow
    below 4 MiB included). `image` ties the spec's starting state to those seeds; `BootRamZeroClaim` derives from it
    that every tracked RAM cell starts at 0. `projection` selects the standard or the extended decoder metadata. -/
structure RVPooledBootInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (inits : List (InitsTeardowns.Witness p InitsTeardowns.importedLayout))
    (projection : RV.Instr → Option (DecoderData PooledFamily) := rvPooledDecoderFields) : Prop where
  /-- Every RV32 register, including x0, is in the public tracked domain. -/
  registers : ∀ index, Cell.register index ∈ cells
  /-- The public domain has no repeated cells. -/
  distinct : cells.Nodup
  /-- Tracked RAM cells are aligned words. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Public code bytes read by `RV.read` and decoded by `RV.decode` build every program entry. -/
  programImage : ∃ addresses, rvProgramImageWith projection initial addresses = some program
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
    InitsTeardowns.windowCells InitsTeardowns.importedLayout (inits.flatMap fun w => w.topBits.toList)
  /-- Reading the tracked cells of the starting state gives the native seeds. -/
  image : initialImageRV initial cells = some trace.initialMemory
  /-- The native machine starts at PC zero and clock four. -/
  initialBoundary : trace.initial = PCState.boundary 0 (4, 0)
  /-- Modeled word-ROM queries hold the ROM image's words at the public ROM cells. -/
  wordTable : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells)
  /-- Subword ROM lookups use the ROM image of the starting state. -/
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial)
  /-- The unresolved jump/teardown endpoint condition: both final PC limbs are 16-bit (JumpBranchSlt does not
      range-check the outgoing PC's high limb; every other row's outgoing PC is the next row's decoder-table PC). -/
  terminalPC : trace.terminal.word.Bounded

end Airbender.Trace
