import Airbender.Proofs.GKRProtocol.DecoderTail.AddSub.Rows
import Airbender.Proofs.GKRProtocol.DecoderSetupRefinement
import Airbender.Proofs.Tables.Decoder.AddSub

namespace Airbender.Compiler.DecoderTail.AddSub.Membership
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Rows.nativeSetup

theorem leading_rows (row : Fin 16777216) (leading : row.val < addSubSetup.offset) :
    addSubSetup.tagged = true ∧ (normalizeDecoderFields addSubSetup (Rows.nativeRow row))[9] =
      (Setup.signedValue ((addSubSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
  have impossible : row.val < 0 := leading
  omega

theorem tail_rows (row : Fin 16777216) (outside : ¬row.val < addSubSetup.offset) :
    normalizeDecoderFields addSubSetup (Rows.nativeRow row) =
      (addSubSetup.row ⟨row.val - addSubSetup.offset, by have := row.isLt; change row.val - 0 < 16777216; change ¬row.val < 0 at outside; omega⟩).map
        (fun n => (Setup.signedValue n : Source.BaseField)) := by
  have lower : 0 ≤ row.val := by change ¬row.val < 0 at outside; omega
  let index : Fin 16777216 := ⟨row.val - 0, by have := row.isLt; omega⟩
  have position : (⟨0 + index.val, by have := index.isLt; omega⟩ : Fin 16777216) = row := by
    apply Fin.ext
    dsimp [index]
    omega
  have values := (congrArg (normalizeDecoderFields addSubSetup) (congrArg Rows.nativeRow position)).symm.trans (Rows.normalized_tail_row index)
  let packedIndex : Fin (addSubSetup.realRows.length + addSubSetup.padding.length) := ⟨index.val, by exact index.isLt⟩
  have result : normalizeDecoderFields addSubSetup (Rows.nativeRow row) = (addSubSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) := values
  have casts : (addSubSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) =
      (addSubSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField)) := by
    apply Vector.ext
    intro column bound
    simp only [Vector.getElem_map]
    exact (Setup.signedValue_cast _).symm
  change normalizeDecoderFields addSubSetup (Rows.nativeRow row) = (addSubSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField))
  exact result.trans casts

theorem full_lookup (packed : Vector Source.BaseField 8) (query : Vector Source.BaseField 9)
    (normalized : normalizeDecoderFields addSubSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.AddSub").Contains #[] packed) : addSubSetup.lookup query :=
  decoder_full_lookup_of_rows addSubSetup nativeSetup.imported.data (by decide +kernel)
    leading_rows tail_rows packed query normalized _ member

theorem lookup_sound (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (packed : Vector Source.BaseField 8) (query : Vector Source.BaseField 9) (typed : query[0].val < 65536)
    (normalized : normalizeDecoderFields addSubSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.AddSub").Contains #[] packed) :
    (Trace.decoderTable pooledProgram .addSub).Contains #[] query :=
  Trace.NativeDecoder.Proofs.AddSub.lookup_sound capacity query typed (full_lookup packed query normalized member)

end Airbender.Compiler.DecoderTail.AddSub.Membership
