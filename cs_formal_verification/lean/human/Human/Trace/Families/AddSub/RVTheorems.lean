import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Memory.Native
import Human.Helpers.Context.RVBoundary
import Human.Helpers.Context.FamilyLayout
import Human.Trace.RVExecution

/-! RV32 twins of the ADD/SUB and word-memory trace claims (`Theorems.lean`): the accepted rows are a run of our spec
    (`RV.run`) from the public starting state `initial : RV.State`. `SailSoundnessClaim` (unchanged Sail, LW to x0
    excluded) has no twin: in our spec LW to x0 is a no-op (`RV.exec`), which is the Airbender profile, so
    `RVAirbenderSoundnessClaim` covers it. Proven in `slop/Slop/Final/Trace/Families/AddSub/RVTheorems.lean` (checked
    by verify.sh). -/

namespace Airbender.Trace

/-- RV twin of `Decoded`: every row's decoder query is in its family's table built from the RV program. Logical
    membership; lookup enforcement is external. -/
def RVDecoded {p : Nat} [Fact p.Prime] (trace : Data p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program row.family).Contains #[] row.decoderQuery

/-- RV twin of `ExecutionBoundary`, without the Sail-only conditions (`Configured`, `OrdinaryWordAddress`, the
    code-domain guard: the RV program table's fetch guard keeps every row's PC in ROM, aligned) and without the
    register-domain condition (every register a row touches is a tracked cell through the row's own history). The
    modeled word-ROM table holds the ROM image's words (`romImageRV`), not the seed values (RAM, shadow RAM below
    `ROM_END` included). -/
structure RVExecutionBoundary {p : Nat} [Fact p.Prime] (trace : Data p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop
    extends RVNativeInputs rvDecoderFields trace initial cells program where
  /-- Bind the modeled word-ROM table to the ROM image. -/
  rom : trace.rom = ROM.table cells (romImageRV initial cells)

/-- RV twin of `NativeBootBoundary` (as `UnifiedReduced.RVBootInputs`): native boot, PC zero, registers and all of
    RAM zero (shadow RAM below `ROM_END` included, so the zero native seed is the RV image); the ROM image holds the
    program. Sail-only and register-domain conditions are dropped as in `RVExecutionBoundary`. -/
structure RVNativeBootBoundary {p : Nat} [Fact p.Prime] (trace : Data p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop where
  /-- Each tracked register or aligned RAM word occurs once. -/
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Initial PC zero, registers zero, all of RAM zero; the ROM image holds the program. -/
  profile : RVInitialProfile initial cells
  /-- Every tracked cell is readable in the starting state. -/
  image : ∃ image : List (MemoryToken p), initialImageRV initial cells = some image
  /-- Native seed values are zero (the starting RAM and registers). -/
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  /-- Public starting PC zero and native timestamp four. Later clocks are proved. -/
  initialPC : trace.initial = PCState.boundary 0 (4, 0)
  /-- Public ROM bytes (`RV.read` of `rom`) and `RV.decode` construct the program table. -/
  programImage : ∃ addresses, rvProgramImageWith rvDecoderFields initial addresses = some program
  /-- Bind the modeled word-ROM table to the ROM image. -/
  rom : trace.rom = ROM.table cells (romImageRV initial cells)

/-- ADD/SUB and word-memory rows, in native time order, are a run of `RV.step` from `initial` reaching the terminal
    PC and cell values (LW to x0 is a no-op in our spec: the Airbender profile). -/
def RVAirbenderSoundnessClaim : Prop :=
  ∀ {trace : Data babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry} (inputs : RVExecutionBoundary trace initial cells program) (accepted : Accepted trace) (decoded : RVDecoded trace program),
    RVRealizes trace initial cells

/-- The same rows from native boot. No ROM view: ROM-range RAM tokens are the shadow RAM, zero at boot. -/
def RVNativeBootSoundnessClaim : Prop :=
  ∀ {trace : Data babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry} (inputs : RVNativeBootBoundary trace initial cells program) (accepted : Accepted trace) (decoded : RVDecoded trace program),
    RVRealizes trace initial cells

end Airbender.Trace
