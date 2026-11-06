import Airbender.Proofs.Trace.Families.ReducedMachine.Sources

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Public initialization, native matching and original shift decoding derive
    the actual source bounds and canonical limb/amount/direction packing.
    No source-range, packed-key or expected-read answer is an input. -/
theorem public_shift_source_keys {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before shiftDecoderFields ∧
      row.decoderQuery = entry.query ∧ ShiftDecoded row.assignment entry ∧
      ∀ limb : Fin 2,
        (entry.data.family.lookupKey (source1 row.assignment)[limb] (shiftAmount row.assignment)).val =
          (source1 row.assignment)[limb].val + 65536 * (shiftAmount row.assignment).val +
            2097152 * (if entry.data.family = .left then 0 else 1) :=
  NativeShiftRangeProofs.image_source_keys image inputs accepted decoded row present

end Airbender.ReducedMachine.Native
