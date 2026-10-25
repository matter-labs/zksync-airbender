import GKRProtocol.CanonicalSource
import GKRProtocol.SourceFields
import GKRProtocol.BaseEncoding

namespace Airbender.Compiler
set_option warningAsError true

def SourceLookupQuery.usedFields (query : SourceLookupQuery) : List Source.EncodedField :=
  query.fields ++ query.mask.toList

theorem SourceLookupQuery.value_congr {R : Type} [CommRing R] (query : SourceLookupQuery)
    (hom : Source.BaseField →+* R) (alpha gamma : R)
    (left right : Nat → Source.BaseField)
    (same : ∀ field ∈ query.usedFields, field.value left = field.value right) :
    query.value hom alpha gamma left = query.value hom alpha gamma right := by
  have fields : query.fields.map (fun field => field.value left) =
      query.fields.map (fun field => field.value right) :=
    List.map_congr_left (fun field member => same field (List.mem_append_left _ member))
  have weight : query.weight hom left = query.weight hom right := by
    cases mask : query.mask with
    | none => simp only [weight, mask]
    | some field =>
        simp only [weight, mask]
        exact congrArg hom (same field (List.mem_append_right _ (by simp [mask])))
  simp only [value, fields, weight]

theorem Source.EncodedField.frame_value (field : Source.EncodedField)
    (placement : Nat → Fin n) (coordinates : List (Fin n))
    (checked : erasureUntouched coordinates (field.polynomial placement) = true)
    (left right : Fin n → Source.BaseField)
    (same : ∀ index, index ∉ coordinates → left index = right index) :
    field.value (left ∘ placement) = field.value (right ∘ placement) := by
  rw [← field.polynomial_value, ← field.polynomial_value]
  apply evaluate_congr_on
  intro term member wire included
  apply same
  have outside := List.all_eq_true.mp (List.all_eq_true.mp checked term member) wire included
  simpa using outside

def Source.EncodedField.transportCheck (field : Source.EncodedField)
    (sourcePlacement : Nat → Fin n) (nativePlacement : Nat → Fin m)
    (inputBank : WireBank n) (nativeBank : WireBank m) : Bool :=
  let polynomial := field.polynomial nativePlacement
  polynomial.all (fun term => term.2.all (fun wire =>
    decide (inputBank.address (inputBank.placement (nativeBank.address wire)) = nativeBank.address wire))) &&
    decide (rename (inputBank.placement ∘ nativeBank.address) polynomial = field.polynomial sourcePlacement)

theorem Source.EncodedField.transport_value (field : Source.EncodedField)
    (sourcePlacement : Nat → Fin n) (nativePlacement : Nat → Fin m)
    (inputBank : WireBank n) (nativeBank : WireBank m)
    (checked : field.transportCheck sourcePlacement nativePlacement inputBank nativeBank = true)
    (source : Fin n → Source.BaseField) (base : GKRAddress → Source.BaseField)
    (inputs : ∀ wire, base (inputBank.address wire) = source wire) :
    field.value ((base ∘ nativeBank.address) ∘ nativePlacement) = field.value (source ∘ sourcePlacement) := by
  have parts : (field.polynomial nativePlacement).all (fun term => term.2.all (fun wire =>
      decide (inputBank.address (inputBank.placement (nativeBank.address wire)) = nativeBank.address wire))) = true ∧
      rename (inputBank.placement ∘ nativeBank.address) (field.polynomial nativePlacement) =
        field.polynomial sourcePlacement := by
    simpa only [transportCheck, Bool.and_eq_true, decide_eq_true_eq] using checked
  rw [← field.polynomial_value, ← field.polynomial_value, ← parts.2, evaluate_rename]
  apply evaluate_congr_on
  intro term member wire included
  have roundTrip : inputBank.address (inputBank.placement (nativeBank.address wire)) = nativeBank.address wire :=
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp parts.1 term member) wire included)
  exact (congrArg base roundTrip).symm.trans (inputs _)

end Airbender.Compiler
