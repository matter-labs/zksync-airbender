import Human.Trace.RVExecution
import Human.Helpers.Context.RVBoundary
import Human.Helpers.Context.Registries.SubwordMemory
import Human.Circuits.SubwordMemory.RVDecoder
import Human.Helpers.Memory.ROM
import Human.Helpers.Tables.Subword

/-! RV32 twin of `RamTraceSoundnessClaim` (`Theorems.lean`): the accepted rows are a run of our spec (`RV.run`) from
    the public starting state `initial : RV.State`. Proven in
    `slop/Slop/Final/Trace/Families/SubwordMemory/RVTheorems.lean` (checked by verify.sh). -/

namespace Airbender.SubwordMemory
open Trace

/-- RV twin of `Decoded`: every row's decoder query is in the family table built from the RV program. Logical
    membership; lookup enforcement is external. -/
def RVDecoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program).Contains #[] (decoderQuery row.assignment)

/-- RV twin of `RAMInputs`, without the Sail-only `Configured`, `OrdinaryWordAddress` and code-domain conditions (the
    RV program table's fetch guard keeps every row's PC in ROM, aligned). -/
structure RVRAMInputs {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop
    extends RVNativeInputs rvDecoderFields trace initial cells program where
  /-- RAM only: every tracked RAM cell lies at or above the ROM region, so no row loads from ROM. -/
  ramDomain : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat
  /-- The modeled subword ROM table has the subword-table shape (its values are never read: rows load RAM). -/
  setup : ∃ values, trace.rom = Verification.subwordTable values

/-- RAM LB/LBU/LH/LHU/SB/SH rows, in native time order, are a run of `RV.step` from `initial` reaching the terminal
    PC and cell values. Global history supplies all input bounds and reads; the boundary has no per-row assumptions. -/
def RVRamTraceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} (inputs : RVRAMInputs trace initial cells program) (accepted : Trace.Accepted trace) (decoded : RVDecoded trace program),
    Trace.RVRealizes trace initial cells

end Airbender.SubwordMemory
