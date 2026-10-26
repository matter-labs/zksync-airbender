import Airbender.Proofs.GKRProtocol.DecoderArguments
import Airbender.Review.Helpers.Decoder.NativeData

namespace Airbender.Compiler
open Airbender.Trace.NativeDecoder
set_option warningAsError true

/-- Apply actual imported packing metadata to a base-field query. -/
def normalizeDecoderFields (setup : PackedSetup) (packed : Vector Source.BaseField setup.width) :
    Vector Source.BaseField 10 :=
  Vector.ofFn fun column =>
    if column.val < 9 then
      if setup.columnsMask[column.val]?.getD false then
        packed.toArray[((setup.columnsMask.extract 0 column.val).filter id).size]?.getD 0
      else 0
    else if setup.tagged then packed.toArray[setup.width - 1]?.getD 0 else 46

private theorem option_getD_cast (value : Option Nat) :
    ((value.map (fun n : Nat => (n : Source.BaseField))).getD 0) =
      ((value.getD 0 : Nat) : Source.BaseField) := by
  cases value <;> rfl

theorem normalize_decoder_fields_cast (setup : PackedSetup) (packed : Vector Nat setup.width) :
    normalizeDecoderFields setup (packed.map (fun n : Nat => (n : Source.BaseField))) =
      (setup.normalize packed).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [normalizeDecoderFields, PackedSetup.normalize, Vector.getElem_ofFn,
    Vector.getElem_map, Vector.toArray_map, Array.getElem?_map]
  split_ifs <;> simp only [option_getD_cast, Nat.cast_zero, Nat.cast_ofNat]

end Airbender.Compiler
