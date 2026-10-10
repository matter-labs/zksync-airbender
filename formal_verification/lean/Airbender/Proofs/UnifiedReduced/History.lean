import Airbender.Review.UnifiedReduced.Memory
import Airbender.Proofs.UnifiedReduced.ZeroRegister
import Airbender.Proofs.UnifiedReduced.Values

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
      (fetched hp image core (decoded _ member))

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

end Airbender.UnifiedReduced.Proofs
