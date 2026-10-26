import Airbender.Proofs.GKRProtocol.QueryFrame

namespace Airbender.Compiler
set_option warningAsError true

theorem decoder_fields_congr (query : SourceLookupQuery) (left right : Nat → Source.BaseField)
    (same : ∀ field ∈ query.usedFields, field.value left = field.value right) :
    query.fields.map (fun field => field.value left) = query.fields.map (fun field => field.value right) :=
  List.map_congr_left (fun field member => same field (List.mem_append_left _ member))

theorem decoder_weight_congr (query : SourceLookupQuery) (left right : Nat → Source.BaseField)
    (same : ∀ field ∈ query.usedFields, field.value left = field.value right) :
    query.weight (RingHom.id _) left = query.weight (RingHom.id _) right := by
  cases selected : query.mask with
  | none => simp only [SourceLookupQuery.weight, selected]
  | some field =>
    simp only [SourceLookupQuery.weight, selected, RingHom.id_apply]
    exact same field (List.mem_append_right _ (by simp [selected]))

end Airbender.Compiler
