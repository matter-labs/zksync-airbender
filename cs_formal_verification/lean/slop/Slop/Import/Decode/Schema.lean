module
public import Slop.Import.Decode.Basic

@[expose] public section

/-! Every schema type's decoder is lawful, by the combinator lemmas of `Basic.lean`. -/

namespace Airbender.Decode
open Json (Value)
open Serde (encode)

instance : Lawful ColumnRange := ⟨struct_lawful (fun s => (s.start, s.«end», ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : LawfulKey OutputType := ⟨unitKey_lawful _
  (forall_mem_cons' rfl <| forall_mem_cons' rfl <| forall_mem_cons' rfl <| forall_mem_cons' rfl <|
    forall_mem_cons' rfl <| forall_mem_nil')
  (fun | .PermutationProduct | .Lookup16Bits | .LookupTimestamps | .GenericLookup | .InitsAndTeardownsProduct => rfl)⟩

instance : Lawful VirtualSetupPoly := ⟨variants_lawful _ _
  (forall_mem_cons' rfl <| forall_mem_cons' rfl <| forall_mem_cons' rfl <| forall_mem_cons' rfl <| forall_mem_nil')
  (forall_mem_nil')
  (fun
    | .RangeCheck16Bits => rfl
    | .RangeCheckTimestamp => rfl
    | .InitsAndTeardownsLow => rfl
    | .InitsAndTeardownsHigh => rfl)⟩

instance : Lawful GKRAddress := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .BaseLayerWitness x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .BaseLayerMemory x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .InnerLayer x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .Setup x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .VirtualSetup x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .ScratchSpace x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .Cached x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ())))⟩

instance : Lawful LinearRelation := ⟨struct_lawful (fun s => (s.linear_terms, s.constant, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful SingleColumnLookupRelation := ⟨struct_lawful (fun s => (s.input, s.lookup_set_index, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful VectorLookupRelation := ⟨struct_lawful (fun s => (s.columns, s.lookup_set_index, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful CompiledMaxQuadraticGKRRelation := ⟨struct_lawful (fun s => (s.quadratic_terms, s.linear_terms, s.constant, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful CompiledAddressSpaceRelationStrict := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .Constant x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .IsRegister x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .IsRam x => (variants_tag rfl _).trans (newtype_encode _ x))⟩

instance : Lawful CompiledAddressStrict := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .ConstantU16 x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .Constant x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .U16Space x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .U32Space x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .U32SpaceSpecialIndirect x0 x1 x2 x3 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, x3, ()))
    | .U32SpaceGeneric x => (variants_tag rfl _).trans (newtype_encode _ x))⟩

instance : Lawful CompiledMemoryTimestamp := ⟨variants_lawful _ _
  (forall_mem_cons' rfl <| forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .Normal x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .Zero => rfl)⟩

instance : Lawful RamWordRepresentation := ⟨variants_lawful _ _
  (forall_mem_cons' rfl <| forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .U16Limbs x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .U8Limbs x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .Zero => rfl)⟩

instance : Lawful SpecialMemoryContributionRelation := ⟨struct_lawful (fun s => (s.address_space, s.address, s.timestamp, s.value, s.timestamp_offset, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful MaxQuadraticConstraintsGKRRelation := ⟨struct_lawful (fun s => (s.quadratic_terms, s.linear_terms, s.constants, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful InitsOrTeardownsTimestampAndValue := ⟨variants_lawful _ _
  (forall_mem_cons' rfl <| forall_mem_nil')
  (forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .Teardown x0 x1 x2 x3 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, x3, ()))
    | .Init => rfl)⟩

/-! `StructuredExpression`: decoded by structural recursion, so lawful by recursion on the value (soundness) and on the
expression (completeness). -/

theorem StructuredExpression.encode_constant (c : Coefficient) : encode (StructuredExpression.Constant c) = Json.tag "Constant" (encode c) := by
  show StructuredExpression.encode _ = _; rw [StructuredExpression.encode]

theorem StructuredExpression.encode_place (x : GKRAddress) : encode (StructuredExpression.Place x) = Json.tag "Place" (encode x) := by
  show StructuredExpression.encode _ = _; rw [StructuredExpression.encode]

theorem StructuredExpression.encode_sum (l : List StructuredExpression) : encode (StructuredExpression.Sum ⟨l⟩) = Json.tag "Sum" (.arr (l.map encode)) := by
  show StructuredExpression.encode _ = _; rw [StructuredExpression.encode]; rfl

theorem StructuredExpression.encode_product (l : List StructuredExpression) :
    encode (StructuredExpression.Product ⟨l⟩) = Json.tag "Product" (.arr (l.map encode)) := by
  show StructuredExpression.encode _ = _; rw [StructuredExpression.encode]; rfl

mutual
theorem StructuredExpression.decode_sound : ∀ (v : Value) (a : StructuredExpression), StructuredExpression.decode v = .ok a → encode a = v
  | .obj [(k, p)], a, h => by
    rw [StructuredExpression.decode] at h
    split at h
    · rename_i hk; subst hk; obtain ⟨x, hx, rfl⟩ := map_ok.1 h
      rw [StructuredExpression.encode_constant, (Lawful.iff p x).1 hx]; rfl
    split at h
    · rename_i hk; subst hk; obtain ⟨x, hx, rfl⟩ := map_ok.1 h
      rw [StructuredExpression.encode_place, (Lawful.iff p x).1 hx]; rfl
    split at h
    · rename_i hk; subst hk; obtain ⟨⟨l⟩, hx, rfl⟩ := map_ok.1 h
      rw [StructuredExpression.encode_sum, ← StructuredExpression.decodeArray_sound p ⟨l⟩ hx]; rfl
    split at h
    · rename_i hk; subst hk; obtain ⟨⟨l⟩, hx, rfl⟩ := map_ok.1 h
      rw [StructuredExpression.encode_product, ← StructuredExpression.decodeArray_sound p ⟨l⟩ hx]; rfl
    exact absurd h (fail_ne _ _)
  | .null, _, h | .bool _, _, h | .int _, _, h | .str _, _, h | .arr _, _, h | .obj [], _, h
  | .obj (_ :: _ :: _), _, h => by simp [StructuredExpression.decode, fail] at h
theorem StructuredExpression.decodeArray_sound : ∀ (v : Value) (xs : Array StructuredExpression), StructuredExpression.decodeArray v = .ok xs →
    .arr (xs.toList.map encode) = v
  | .arr vs, xs, h => by
    rw [StructuredExpression.decodeArray] at h
    obtain ⟨l, hl, rfl⟩ := map_ok.1 h
    rw [List.toList_toArray, StructuredExpression.decodeList_sound vs l hl]
  | .null, _, h | .bool _, _, h | .int _, _, h | .str _, _, h | .obj _, _, h => by simp [StructuredExpression.decodeArray, fail] at h
theorem StructuredExpression.decodeList_sound : ∀ (vs : List Value) (l : List StructuredExpression), StructuredExpression.decodeList vs = .ok l → l.map encode = vs
  | [], l, h => by rw [StructuredExpression.decodeList] at h; cases h; rfl
  | v :: vs, l, h => by
    rw [StructuredExpression.decodeList] at h
    obtain ⟨a, ha, h⟩ := bind_ok.1 h
    obtain ⟨l', hl', h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [List.map_cons, StructuredExpression.decode_sound v a ha, StructuredExpression.decodeList_sound vs l' hl']
end

mutual
theorem StructuredExpression.decode_complete : ∀ a : StructuredExpression, StructuredExpression.decode (encode a) = .ok a
  | .Constant c => by
    rw [StructuredExpression.encode_constant, Json.tag, StructuredExpression.decode]; simp [decode_encode]; rfl
  | .Place x => by
    rw [StructuredExpression.encode_place, Json.tag, StructuredExpression.decode]; simp [decode_encode]; rfl
  | .Sum ⟨l⟩ => by
    rw [StructuredExpression.encode_sum, Json.tag, StructuredExpression.decode]
    simp [StructuredExpression.decodeArray, StructuredExpression.decodeList_complete l]; rfl
  | .Product ⟨l⟩ => by
    rw [StructuredExpression.encode_product, Json.tag, StructuredExpression.decode]
    simp [StructuredExpression.decodeArray, StructuredExpression.decodeList_complete l]; rfl
theorem StructuredExpression.decodeList_complete : ∀ l : List StructuredExpression, StructuredExpression.decodeList (l.map encode) = .ok l
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, StructuredExpression.decodeList, StructuredExpression.decode_complete a, StructuredExpression.decodeList_complete l]; rfl
end

instance : Lawful StructuredExpression :=
  ⟨fun v a => ⟨StructuredExpression.decode_sound v a, fun h => h ▸ StructuredExpression.decode_complete a⟩⟩

instance : Lawful GKRRelation := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .LinearBaseFieldRelation x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .MaxQuadratic x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .EnforceSingleMaxQuadraticConstraint x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .EnforceConstraintsMaxQuadratic x0 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ done_lawful) (x0, ()))
    | .CopyInBaseField x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .CopyInExtensionField x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .InitialGrandProductFromCaches x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .InitialGrandProductWithoutCaches x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .UnbalancedGrandProductWithCache x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .MaterializeGrandProductTermExpression x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .TrivialProduct x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .MaskIntoIdentityProduct x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .MaterializeSingleLookupInput x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .MaterializedVectorLookupInput x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .LookupWithCachedDensAndSetup x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .LookupWithDensAndSetupExpressions x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .LookupPairFromBaseInputs x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .LookupPairFromMaterializedBaseInputs x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .LookupFromBaseInputsWithSetup x0 x1 x2 x3 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, x3, ()))
    | .LookupFromMaterializedBaseInputWithSetup x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .LookupUnbalancedPairWithMaterializedBaseInputs x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .LookupPairFromVectorInputs x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .LookupPairFromMaterializedVectorInputs x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .LookupFromVectorInputWithSetup x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .LookupFromMaterializedVectorInputWithSetup x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .LookupPairFromCachedVectorInputs x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .LookupUnbalancedPairWithVectorInputs x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .LookupUnbalancedPairWithMaterializedVectorInputs x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .AggregateLookupRationalPair x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .InitsOrTeardownsInitialPair x0 x1 x2 x3 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, x3, ())))⟩

instance : Lawful GKRCacheRelation := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .SingleColumnLookup x0 x1 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ done_lawful) (x0, x1, ()))
    | .VectorizedLookup x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .MemoryTuple x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .VectorizedLookupSetup x => (variants_tag rfl _).trans (newtype_encode _ x))⟩

instance : Lawful GateArtifacts := ⟨struct_lawful (fun s => (s.output_layer, s.enforced_relation, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : NotNull RamAuxComparisonSet := ⟨fun _ => nofun⟩
instance : Lawful RamAuxComparisonSet := ⟨struct_lawful (fun s => (s.intermediate_borrow, ()))
  (field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful RelativeTimestampGroup := ⟨struct_lawful (fun s => (s.read_timestamp, s.members, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful GKRAuxLayoutData := ⟨struct_lawful
  (fun s => (s.shuffle_ram_timestamp_comparison_aux_vars, s.relative_timestamp_groups, ()))
  (field_lawful _ <| optField_lawful _ done_lawful fun _ _ => nofun)
  (fun _ => rfl) (fun _ => rfl) (fun ⟨_, o⟩ => by cases o <;> rfl)⟩

instance : Lawful GKRLayerDescription := ⟨struct_lawful (fun s => (s.layer, s.gates_with_external_connections, s.cached_relations, s.gates, s.intermediate_layer_width, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful RegisterOnlyAccessAddress := ⟨struct_lawful (fun s => (s.register_index, ()))
  (field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful RegisterOrRamAddressSpace := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .RegisterAddressSpace x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .RamAddressSpace x => (variants_tag rfl _).trans (newtype_encode _ x))⟩

instance : Lawful RegisterOrRamAccessAddress := ⟨struct_lawful (fun s => (s.address_space, s.address, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful IndirectRamAccessAddress := ⟨struct_lawful (fun s => (s.base_register_value, s.base_register_index, s.constant_offset, s.indirect_access_idx_for_register, s.variable_offset, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful RamAddress := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .ConstantRegister x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .RegisterOnly x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .RegisterOrRam x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .IndirectRam x => (variants_tag rfl _).trans (newtype_encode _ x))⟩

instance : Lawful RamReadQuery := ⟨struct_lawful (fun s => (s.in_cycle_write_index, s.address, s.read_timestamp, s.read_value, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful RamWriteQuery := ⟨struct_lawful (fun s => (s.in_cycle_write_index, s.address, s.read_timestamp, s.read_value, s.write_value, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful RamQuery := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .Readonly x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .Write x => (variants_tag rfl _).trans (newtype_encode _ x))⟩

instance : Lawful GKRMachineState := ⟨struct_lawful (fun s => (s.pc, s.timestamp, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : NotNull MachineStatePermutationDescription := ⟨fun _ => nofun⟩
instance : Lawful MachineStatePermutationDescription := ⟨struct_lawful (fun s => (s.execute, s.initial_state, s.final_state, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : NotNull CompiledDelegationCircuitState := ⟨fun _ => nofun⟩
instance : Lawful CompiledDelegationCircuitState := ⟨struct_lawful (fun s => (s.execute, s.invocation_timestamp, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : NotNull DecoderPlacementDescription := ⟨fun _ => nofun⟩
instance : Lawful DecoderPlacementDescription := ⟨struct_lawful (fun s => (s.rs1_index, s.rs2_index, s.rd_index, s.circuit_family_mask_bits, s.decoder_witness_is_in_memory, s.imm, s.funct3, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful GKRMemoryLayout := ⟨struct_lawful (fun s => (s.ram_access_sets, s.machine_state, s.delegation_state, s.decoder_input, s.indirect_access_variable_offsets, s.teardown_sets, s.total_width, s.inits_and_teardowns_word_bits, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful GKRWitnessLayout := ⟨struct_lawful (fun s => (s.multiplicities_columns_for_range_check_16, s.multiplicities_columns_for_timestamp_range_check, s.multiplicities_columns_for_generic_lookup, s.total_width, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful Degree1Constraint := ⟨struct_lawful (fun s => (s.linear_terms, s.constant_term, ()))
  (field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful Degree2Constraint := ⟨struct_lawful (fun s => (s.quadratic_terms, s.linear_terms, s.constant_term, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

instance : Lawful Term := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (newtype_sound (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .Constant x => (variants_tag rfl _).trans (newtype_encode _ x)
    | .Expression x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ())))⟩

instance : Lawful Constraint := ⟨struct_lawful (fun s => (s.terms, ()))
  (field_lawful _ done_lawful)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

/-! `Expr`: decoded by structural recursion, so lawful by recursion on the value (soundness) and on the
expression (completeness). -/

theorem Expr.encode_constant (c : Coefficient) : encode (Expr.Constant c) = Json.tag "Constant" (encode c) := by
  show Expr.encode _ = _; rw [Expr.encode]

theorem Expr.encode_var (x : Nat) : encode (Expr.Var x) = Json.tag "Var" (encode x) := by
  show Expr.encode _ = _; rw [Expr.encode]

theorem Expr.encode_sum (l : List Expr) : encode (Expr.Sum ⟨l⟩) = Json.tag "Sum" (.arr (l.map encode)) := by
  show Expr.encode _ = _; rw [Expr.encode]; rfl

theorem Expr.encode_product (l : List Expr) :
    encode (Expr.Product ⟨l⟩) = Json.tag "Product" (.arr (l.map encode)) := by
  show Expr.encode _ = _; rw [Expr.encode]; rfl

mutual
theorem Expr.decode_sound : ∀ (v : Value) (a : Expr), Expr.decode v = .ok a → encode a = v
  | .obj [(k, p)], a, h => by
    rw [Expr.decode] at h
    split at h
    · rename_i hk; subst hk; obtain ⟨x, hx, rfl⟩ := map_ok.1 h
      rw [Expr.encode_constant, (Lawful.iff p x).1 hx]; rfl
    split at h
    · rename_i hk; subst hk; obtain ⟨x, hx, rfl⟩ := map_ok.1 h
      rw [Expr.encode_var, (Lawful.iff p x).1 hx]; rfl
    split at h
    · rename_i hk; subst hk; obtain ⟨⟨l⟩, hx, rfl⟩ := map_ok.1 h
      rw [Expr.encode_sum, ← Expr.decodeArray_sound p ⟨l⟩ hx]; rfl
    split at h
    · rename_i hk; subst hk; obtain ⟨⟨l⟩, hx, rfl⟩ := map_ok.1 h
      rw [Expr.encode_product, ← Expr.decodeArray_sound p ⟨l⟩ hx]; rfl
    exact absurd h (fail_ne _ _)
  | .null, _, h | .bool _, _, h | .int _, _, h | .str _, _, h | .arr _, _, h | .obj [], _, h
  | .obj (_ :: _ :: _), _, h => by simp [Expr.decode, fail] at h
theorem Expr.decodeArray_sound : ∀ (v : Value) (xs : Array Expr), Expr.decodeArray v = .ok xs →
    .arr (xs.toList.map encode) = v
  | .arr vs, xs, h => by
    rw [Expr.decodeArray] at h
    obtain ⟨l, hl, rfl⟩ := map_ok.1 h
    rw [List.toList_toArray, Expr.decodeList_sound vs l hl]
  | .null, _, h | .bool _, _, h | .int _, _, h | .str _, _, h | .obj _, _, h => by simp [Expr.decodeArray, fail] at h
theorem Expr.decodeList_sound : ∀ (vs : List Value) (l : List Expr), Expr.decodeList vs = .ok l → l.map encode = vs
  | [], l, h => by rw [Expr.decodeList] at h; cases h; rfl
  | v :: vs, l, h => by
    rw [Expr.decodeList] at h
    obtain ⟨a, ha, h⟩ := bind_ok.1 h
    obtain ⟨l', hl', h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [List.map_cons, Expr.decode_sound v a ha, Expr.decodeList_sound vs l' hl']
end

mutual
theorem Expr.decode_complete : ∀ a : Expr, Expr.decode (encode a) = .ok a
  | .Constant c => by
    rw [Expr.encode_constant, Json.tag, Expr.decode]; simp [decode_encode]; rfl
  | .Var x => by
    rw [Expr.encode_var, Json.tag, Expr.decode]; simp [decode_encode]; rfl
  | .Sum ⟨l⟩ => by
    rw [Expr.encode_sum, Json.tag, Expr.decode]
    simp [Expr.decodeArray, Expr.decodeList_complete l]; rfl
  | .Product ⟨l⟩ => by
    rw [Expr.encode_product, Json.tag, Expr.decode]
    simp [Expr.decodeArray, Expr.decodeList_complete l]; rfl
theorem Expr.decodeList_complete : ∀ l : List Expr, Expr.decodeList (l.map encode) = .ok l
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, Expr.decodeList, Expr.decode_complete a, Expr.decodeList_complete l]; rfl
end

instance : Lawful Expr :=
  ⟨fun v a => ⟨Expr.decode_sound v a, fun h => h ▸ Expr.decode_complete a⟩⟩

instance : Lawful StructuredStatement := ⟨variants_lawful _ _
  (forall_mem_nil')
  (forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_cons' (fields_sound (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (fun _ => rfl)) <|
    forall_mem_nil')
  (fun
    | .AssertZero x0 x1 x2 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, ()))
    | .Define x0 x1 x2 x3 => (variants_tag rfl _).trans
        (struct_obj (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful) (x0, x1, x2, x3, ())))⟩

instance : Lawful GKRCircuitArtifact := ⟨struct_lawful
  (fun s => (s.trace_len, s.table_offsets, s.total_tables_size, s.offset_for_decoder_table, s.has_decoder_lookup, s.layers, s.global_output_map, s.memory_layout, s.witness_layout, s.scratch_space_size, s.num_generic_lookups, s.placement_data, s.generic_lookup_tables_width, s.decode_table_columns_mask, s.tables_ids_in_generic_lookups, s.generic_lookup_padding, s.degree_2_constraints, s.degree_1_constraints, s.structured_statements, s.generic_lookups, s.range_check_16_lookup_expressions, s.timestamp_range_check_lookup_expressions, s.variable_names, s.scratch_space_mapping, s.scratch_space_mapping_rev, s.aux_layout_data, s._marker, ()))
  (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| optField_lawful _ (field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ <| field_lawful _ done_lawful)
    fun _ _ h => absurd (Prod.mk.inj (Option.some.inj h)).1 (by decide))
  (fun _ => rfl) (fun _ => rfl) (fun c => by rcases c with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _, _, _, _, _, _, _, _, _, _⟩ <;> rfl)⟩


end Airbender.Decode
