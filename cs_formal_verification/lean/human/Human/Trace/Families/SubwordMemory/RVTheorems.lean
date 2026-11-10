module
public import Human.Trace.RVExecution
public import Human.Helpers.Context.RVBoundary
public import Human.Helpers.Context.Registries.SubwordMemory
public import Human.Circuits.SubwordMemory.RVDecoder
public import Human.Helpers.Memory.ROM
public import Human.Helpers.Tables.Subword
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! RAM trace claim: the accepted rows are a run of our spec (`RV.run`) from
    the public starting state `initial : RV.State`. Proven in
    `slop/Slop/Final/Trace/Families/SubwordMemory/RVTheorems.lean` (checked by verify.sh). -/

namespace Airbender.SubwordMemory
open Trace

/-- Every row's decoder query is in the family table built from the RV program. Logical
    membership; lookup enforcement is external. -/
def RVDecoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program).Contains #[] (decoderQuery row.assignment)

/-- Public inputs for RAM rows. No machine-configuration, memory-map or code-domain premise is needed (the
    RV program table's fetch guard keeps every row's PC in ROM, aligned). -/
structure RVRAMInputs {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop
    extends RVNativeInputs rvDecoderFields trace initial cells program where
  /-- RAM only: every tracked RAM cell lies at or above the ROM region, so no row loads from ROM. -/
  ramDomain : ∀ address, Cell.ram address ∈ cells → RV.ROM_END ≤ address.toNat
  /-- The modeled subword ROM table has the subword-table shape (its values are never read: rows load RAM). -/
  setup : ∃ values, trace.rom = Verification.subwordTable values

/-- RAM LB/LBU/LH/LHU/SB/SH rows, in native time order, are a run of `RV.step` from `initial` reaching the terminal
    PC and cell values. Global history supplies all input bounds and reads; the boundary has no per-row assumptions. -/
def RVRamTraceSoundnessClaim : Prop :=
  ∀ {trace : NativeTrace babyBearModulus} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} (_inputs : RVRAMInputs trace initial cells program) (_accepted : Trace.Accepted trace) (_decoded : RVDecoded trace program),
    Trace.RVRealizes trace initial cells

end Airbender.SubwordMemory
