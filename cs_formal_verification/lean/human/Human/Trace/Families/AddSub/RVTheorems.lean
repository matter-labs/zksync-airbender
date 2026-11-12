module
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Memory.Native
public import Human.Helpers.Context.RVBoundary
public import Human.Helpers.Context.RVPooledBoundary
public import Human.Helpers.Context.FamilyLayout
public import Human.Trace.RVExecution

@[expose] public section

/-! ADD/SUB and word-memory trace claims: the accepted rows are a run of our spec
    (`RV.run`) from the public starting state `initial : RV.State`. In our spec LW to x0 is a no-op (`RV.exec`), as in
    Airbender, so `RVAirbenderSoundnessClaim` needs no load restriction. Proven in `proven/Proven/Final/Trace/Families/AddSub/RVTheorems.lean` (checked
    by verify.sh). -/

namespace Airbender.Trace

/-- Every row's decoder query is in its family's table built from the RV program. Logical
    membership; lookup enforcement is external. -/
def RVDecoded {p : Nat} [Fact p.Prime] (trace : Data p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program row.family).Contains #[] row.decoderQuery

/-- Public boundary of the accepted rows. No machine-configuration, memory-map or code-domain premise is needed (the
    RV program table's fetch guard keeps every row's PC in ROM, aligned), nor a
    register-domain condition (every register a row touches is a tracked cell through the row's own history). The
    modeled word-ROM table holds the ROM image's words (`romImageRV`), not the seed values (RAM, shadow RAM below
    `ROM_END` included). -/
structure RVExecutionBoundary {p : Nat} [Fact p.Prime] (trace : Data p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop
    extends RVNativeInputs rvDecoderFields trace initial cells program where
  /-- Bind the modeled word-ROM table to the ROM image. -/
  rom : trace.rom = ROM.table cells (romImageRV initial cells)

/-- Native boot with the seeds of `RVPooledBootInputs`: PC zero, registers zero; the
    RAM is seeded by the `Init` tokens of the inits/teardowns instances `inits`, whose public top bits pass the
    verifier's check, so the tracked RAM is the union of their windows (ROM shadow below 4 MiB included) and `image`
    ties the spec's starting state to those seeds (every tracked RAM cell then reads 0, as `BootRamZeroClaim` derives);
    the ROM image holds the program. As in `RVExecutionBoundary`, no register-domain or memory-map premise is needed. -/
structure RVNativeBootBoundary {p : Nat} [Fact p.Prime] (trace : Data p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry)
    (inits : List (InitsTeardowns.Witness p InitsTeardowns.importedLayout)) : Prop where
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
    InitsTeardowns.windowCells InitsTeardowns.importedLayout (inits.flatMap fun w => w.topBits.toList)
  /-- Reading the tracked cells of the starting state gives the native seeds. -/
  image : initialImageRV initial cells = some trace.initialMemory
  /-- Public starting PC zero and native timestamp four. Later clocks are proved. -/
  initialPC : trace.initial = PCState.boundary 0 (4, 0)
  /-- Public ROM bytes (`RV.read` of `rom`) and `RV.decode` construct the program table. -/
  programImage : ∃ addresses, rvProgramImageWith rvDecoderFields initial addresses = some program
  /-- Bind the modeled word-ROM table to the ROM image. -/
  rom : trace.rom = ROM.table cells (romImageRV initial cells)

/-- ADD/SUB and word-memory rows, in native time order, are a run of `RV.step` from `initial` reaching the terminal
    PC and cell values (LW to x0 is a no-op in our spec: the Airbender profile). -/
def RVAirbenderSoundnessClaim : Prop := RVTraceSoundness RVExecutionBoundary RVDecoded

/-- The same rows from native boot (RAM seeded by the inits/teardowns instances `inits`). No ROM view: ROM-range RAM
    tokens are the shadow RAM, zero at boot. -/
def RVNativeBootSoundnessClaim : Prop :=
  ∀ {trace : Data babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)} (_inputs : RVNativeBootBoundary trace initial cells program inits) (_accepted : Accepted trace) (_decoded : RVDecoded trace program),
    RVRealizes trace initial cells

/-- The assumptions of `RVAirbenderSoundnessClaim` can be met, by a trace with a row. -/
def RVAirbenderSoundnessSatisfiableClaim : Prop := RVTraceSatisfiable RVExecutionBoundary RVDecoded

/-- The assumptions of `RVNativeBootSoundnessClaim` can be met, by a trace with a row. -/
def RVNativeBootSoundnessSatisfiableClaim : Prop :=
  ∃ (trace : Data babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    RVNativeBootBoundary trace initial cells program inits ∧ Accepted trace ∧ RVDecoded trace program ∧
      trace.rows ≠ []

end Airbender.Trace
