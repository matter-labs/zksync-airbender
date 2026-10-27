import Slop.UnifiedReduced.Positions
import Human.Trace.UnifiedReduced.Memory
import Slop.UnifiedReduced.ZeroRegister
import Slop.UnifiedReduced.Values
import Slop.Trace.RowContext

namespace Airbender.UnifiedReduced.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem zero_preserving [Fact p.Prime] (hp : 524288 < p) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program) (decoded : Decoded trace program) :
    ZeroPreserving trace := by
  intro row member
  cases row with
  | mk family w =>
    cases family
    have holds := accepted.constraints ⟨.machine, w⟩ member
    have core := Verification.holds_of_sublist holds
      (List.sublist_append_left (importedConstraints trace.rom)
        importedConstraintsTimestampLookups)
    exact row_zero_preserving hp core (accepted.active _ member)
      (fetched hp image (by find_configured) core (decoded _ member))

theorem memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : NativeInputs decoderFields trace before cells program) (decoded : Decoded trace program) :
    MemoryExecution trace before cells := by
  obtain ⟨addresses, image⟩ := inputs.programImage
  have zero := zero_preserving (by dsimp [timestampBase] at hp; omega) accepted image decoded
  exact native_row_history hp inverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned
    (zero_writes_of_preserving hp inverse accepted inputs.clocks inputs.image zero)

theorem row_position [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : NativeInputs decoderFields trace initial cells program) (decoded : Decoded trace program)
    {row : Row p UnifiedFamily} {before : Reference.RiscV.Sail.State}
    (position : RowPosition trace initial cells row before) :
    ∃ events after,
      SailHistory cells events (retiredState initial row.start.word.toBitVec) before ∧
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after :=
  row_position_from_memory hp inverse accepted inputs.clocks
    (memory_execution hp inverse accepted inputs decoded) position

theorem row_position_exists [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : NativeInputs decoderFields trace initial cells program) (decoded : Decoded trace program)
    {row : Row p UnifiedFamily} (member : row ∈ trace.rows) :
    ∃ before, RowPosition trace initial cells row before :=
  row_position_exists_from_memory (memory_execution hp inverse accepted inputs decoded) member

end Airbender.UnifiedReduced.Proofs
