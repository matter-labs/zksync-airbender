-- No need to review: behaviour is fixed by `DecodeClaim` (Human/Import/Theorems.lean).
module
public import Human.Import.Schema
public import Human.Import.Exec.JsonParser

@[expose] public section

/-! The decoders of the schema types: a JSON value to the Lean value whose `Serde.encode` it is. Total, and
structurally recursive (only `StructuredExpression` and `Expr` recurse), so the kernel can evaluate them. -/

namespace Airbender

class Decode (α : Type) where
  decode : Json.Value → Except String α

namespace Decode
open Json (Value)

def fail (what : String) : Except String α := .error s!"expected {what}"

instance : Decode Nat := ⟨fun | .int (.ofNat n) => .ok n | _ => fail "a natural number"⟩
instance : Decode Bool := ⟨fun | .bool b => .ok b | _ => fail "a boolean"⟩
instance : Decode String := ⟨fun | .str s => .ok s | _ => fail "a string"⟩
instance [Decode α] : Decode (Option α) := ⟨fun | .null => .ok none | v => some <$> decode v⟩

/-- Each item. -/
def items [Decode α] : List Value → Except String (List α)
  | [] => .ok []
  | v :: vs => do return (← decode v) :: (← items vs)

instance [Decode α] : Decode (List α) := ⟨fun | .arr vs => items vs | _ => fail "an array"⟩
instance [Decode α] : Decode (Array α) := ⟨fun v => List.toArray <$> (decode v : Except String (List α))⟩
instance [Decode α] [Decode β] : Decode (α × β) :=
  ⟨fun | .arr [a, b] => do return (← decode a, ← decode b) | _ => fail "a pair"⟩
instance : Decode (BoundedNat bound) :=
  ⟨fun v => do let n : Nat ← decode v; if h : n < bound then return ⟨n, h⟩ else fail s!"a number below {bound}"⟩
instance [Decode α] : Decode (Fixed n α) :=
  ⟨fun v => do let a : Array α ← decode v; if h : a.size = n then return ⟨a, h⟩ else fail s!"{n} items"⟩
instance [Decode α] [Decode β] [Decode γ] : Decode (Triple α β γ) :=
  ⟨fun | .arr [a, b, c] => do return ⟨← decode a, ← decode b, ← decode c⟩ | _ => fail "a triple"⟩
instance : Decode JsonNull := ⟨fun | .null => .ok .null | _ => fail "null"⟩
instance : Decode Coefficient := ⟨fun v => Coefficient.mk <$> decode v⟩

/-- The decoder of map keys. -/
class Key (κ : Type) where
  decodeKey : String → Except String κ

/-- A number key: its decimal digits, as `toString` writes them. -/
instance : Key Nat :=
  ⟨fun s => let n := Json.Parser.digitsValue (Json.utf8 s); if toString n = s then .ok n else fail "a number key"⟩

/-- An enum key: one of the variant names. -/
def unitKey (units : List (String × α)) (k : String) : Except String α :=
  match units.lookup k with
  | some a => .ok a
  | none => fail "a variant name"

instance : Key OutputType := ⟨unitKey [("PermutationProduct", .PermutationProduct),
  ("Lookup16Bits", .Lookup16Bits), ("LookupTimestamps", .LookupTimestamps), ("GenericLookup", .GenericLookup),
  ("InitsAndTeardownsProduct", .InitsAndTeardownsProduct)]⟩

/-- Each member, as a map entry. -/
def entries [Key κ] [Decode α] : List (String × Value) → Except String (List (κ × α))
  | [] => .ok []
  | (k, v) :: ms => do return (← Key.decodeKey k, ← decode v) :: (← entries ms)

instance [Key κ] [Decode α] : Decode (ObjectMap κ α) :=
  ⟨fun | .obj ms => (fun l => ⟨l.toArray⟩) <$> entries ms | _ => fail "an object"⟩

/-- A decoder of the members of an object. -/
abbrev Members (α : Type) := List (String × Value) → Except String α

/-- No more members. -/
def done : Members Unit
  | [] => .ok ()
  | (k, _) :: _ => .error s!"unexpected field {k}"

/-- The member `k`, then the rest. -/
def field [Decode α] (k : String) (rest : Members β) : Members (α × β)
  | (k', v) :: ms => if k' = k then do return (← decode v, ← rest ms) else .error s!"expected field {k}, got {k'}"
  | [] => .error s!"missing field {k}"

/-- The member `k` if present (`none` if absent), then the rest. -/
def optField [Decode α] (k : String) (rest : Members β) : Members (Option α × β)
  | [] => do return (none, ← rest [])
  | (k', v) :: ms => if k' = k then do return (some (← decode v), ← rest ms) else do return (none, ← rest ((k', v) :: ms))

/-- A struct: an object with exactly the members `m` reads, in order. -/
def struct (f : α → β) (m : Members α) : Value → Except String β
  | .obj ms => f <$> m ms
  | _ => fail "an object"

/-- A variant with one unnamed field. -/
def newtype [Decode α] (f : α → β) (p : Value) : Except String β := f <$> decode p

/-- An externally tagged enum: `"Name"` for the unit variants, `{"Name": payload}` for the others. -/
def variants (units : List (String × α)) (tagged : List (String × (Value → Except String α))) :
    Value → Except String α
  | .str k => unitKey units k
  | .obj [(k, p)] => match tagged.lookup k with
    | some d => d p
    | none => fail "a variant name"
  | _ => fail "an enum variant"

instance : Decode ColumnRange := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "start" <| field "end" done)⟩

instance : Decode VirtualSetupPoly := ⟨variants [("RangeCheck16Bits", .RangeCheck16Bits), ("RangeCheckTimestamp", .RangeCheckTimestamp), ("InitsAndTeardownsLow", .InitsAndTeardownsLow), ("InitsAndTeardownsHigh", .InitsAndTeardownsHigh)]
  []⟩

instance : Decode GKRAddress := ⟨variants []
  [("BaseLayerWitness", newtype .BaseLayerWitness),
   ("BaseLayerMemory", newtype .BaseLayerMemory),
   ("InnerLayer", struct (fun (x0, x1, ()) => .InnerLayer x0 x1)
      (field "layer" <| field "offset" done)),
   ("Setup", newtype .Setup),
   ("VirtualSetup", newtype .VirtualSetup),
   ("ScratchSpace", newtype .ScratchSpace),
   ("Cached", struct (fun (x0, x1, ()) => .Cached x0 x1)
      (field "layer" <| field "offset" done))]⟩

instance : Decode LinearRelation := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "linear_terms" <| field "constant" done)⟩

instance : Decode SingleColumnLookupRelation := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "input" <| field "lookup_set_index" done)⟩

instance : Decode VectorLookupRelation := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "columns" <| field "lookup_set_index" done)⟩

instance : Decode CompiledMaxQuadraticGKRRelation := ⟨struct (fun (x0, x1, x2, ()) => ⟨x0, x1, x2⟩)
  (field "quadratic_terms" <| field "linear_terms" <| field "constant" done)⟩

instance : Decode CompiledAddressSpaceRelationStrict := ⟨variants []
  [("Constant", newtype .Constant),
   ("IsRegister", newtype .IsRegister),
   ("IsRam", newtype .IsRam)]⟩

instance : Decode CompiledAddressStrict := ⟨variants []
  [("ConstantU16", newtype .ConstantU16),
   ("Constant", newtype .Constant),
   ("U16Space", newtype .U16Space),
   ("U32Space", newtype .U32Space),
   ("U32SpaceSpecialIndirect", struct (fun (x0, x1, x2, x3, ()) => .U32SpaceSpecialIndirect x0 x1 x2 x3)
      (field "low_base" <| field "low_dynamic_offset" <| field "low_offset" <| field "high" done)),
   ("U32SpaceGeneric", newtype .U32SpaceGeneric)]⟩

instance : Decode CompiledMemoryTimestamp := ⟨variants [("Zero", .Zero)]
  [("Normal", newtype .Normal)]⟩

instance : Decode RamWordRepresentation := ⟨variants [("Zero", .Zero)]
  [("U16Limbs", newtype .U16Limbs),
   ("U8Limbs", newtype .U8Limbs)]⟩

instance : Decode SpecialMemoryContributionRelation := ⟨struct (fun (x0, x1, x2, x3, x4, ()) => ⟨x0, x1, x2, x3, x4⟩)
  (field "address_space" <| field "address" <| field "timestamp" <| field "value" <| field "timestamp_offset" done)⟩

instance : Decode MaxQuadraticConstraintsGKRRelation := ⟨struct (fun (x0, x1, x2, ()) => ⟨x0, x1, x2⟩)
  (field "quadratic_terms" <| field "linear_terms" <| field "constants" done)⟩

instance : Decode InitsOrTeardownsTimestampAndValue := ⟨variants [("Init", .Init)]
  [("Teardown", struct (fun (x0, x1, x2, x3, ()) => .Teardown x0 x1 x2 x3)
      (field "lhs_timestamp" <| field "lhs_value" <| field "rhs_timestamp" <| field "rhs_value" done))]⟩

mutual
def StructuredExpression.decode : Value → Except String StructuredExpression
  | .obj [(k, p)] =>
    if k = "Constant" then .Constant <$> Decode.decode p
    else if k = "Place" then .Place <$> Decode.decode p
    else if k = "Sum" then .Sum <$> StructuredExpression.decodeArray p
    else if k = "Product" then .Product <$> StructuredExpression.decodeArray p
    else fail "a StructuredExpression variant"
  | _ => fail "a StructuredExpression"
def StructuredExpression.decodeArray : Value → Except String (Array StructuredExpression)
  | .arr vs => List.toArray <$> StructuredExpression.decodeList vs
  | _ => fail "an array"
def StructuredExpression.decodeList : List Value → Except String (List StructuredExpression)
  | [] => .ok []
  | v :: vs => do return (← StructuredExpression.decode v) :: (← StructuredExpression.decodeList vs)
end

instance : Decode StructuredExpression := ⟨StructuredExpression.decode⟩

instance : Decode GKRRelation := ⟨variants []
  [("LinearBaseFieldRelation", struct (fun (x0, x1, ()) => .LinearBaseFieldRelation x0 x1)
      (field "input" <| field "output" done)),
   ("MaxQuadratic", struct (fun (x0, x1, x2, ()) => .MaxQuadratic x0 x1 x2)
      (field "input" <| field "expression" <| field "output" done)),
   ("EnforceSingleMaxQuadraticConstraint", struct (fun (x0, x1, ()) => .EnforceSingleMaxQuadraticConstraint x0 x1)
      (field "input" <| field "expression" done)),
   ("EnforceConstraintsMaxQuadratic", struct (fun (x0, ()) => .EnforceConstraintsMaxQuadratic x0)
      (field "input" done)),
   ("CopyInBaseField", struct (fun (x0, x1, ()) => .CopyInBaseField x0 x1)
      (field "input" <| field "output" done)),
   ("CopyInExtensionField", struct (fun (x0, x1, ()) => .CopyInExtensionField x0 x1)
      (field "input" <| field "output" done)),
   ("InitialGrandProductFromCaches", struct (fun (x0, x1, ()) => .InitialGrandProductFromCaches x0 x1)
      (field "input" <| field "output" done)),
   ("InitialGrandProductWithoutCaches", struct (fun (x0, x1, ()) => .InitialGrandProductWithoutCaches x0 x1)
      (field "input" <| field "output" done)),
   ("UnbalancedGrandProductWithCache", struct (fun (x0, x1, x2, ()) => .UnbalancedGrandProductWithCache x0 x1 x2)
      (field "scalar" <| field "input" <| field "output" done)),
   ("MaterializeGrandProductTermExpression", struct (fun (x0, x1, ()) => .MaterializeGrandProductTermExpression x0 x1)
      (field "input" <| field "output" done)),
   ("TrivialProduct", struct (fun (x0, x1, ()) => .TrivialProduct x0 x1)
      (field "input" <| field "output" done)),
   ("MaskIntoIdentityProduct", struct (fun (x0, x1, x2, ()) => .MaskIntoIdentityProduct x0 x1 x2)
      (field "input" <| field "mask" <| field "output" done)),
   ("MaterializeSingleLookupInput", struct (fun (x0, x1, x2, ()) => .MaterializeSingleLookupInput x0 x1 x2)
      (field "input" <| field "output" <| field "range_check_width" done)),
   ("MaterializedVectorLookupInput", struct (fun (x0, x1, ()) => .MaterializedVectorLookupInput x0 x1)
      (field "input" <| field "output" done)),
   ("LookupWithCachedDensAndSetup", struct (fun (x0, x1, x2, ()) => .LookupWithCachedDensAndSetup x0 x1 x2)
      (field "input" <| field "setup" <| field "output" done)),
   ("LookupWithDensAndSetupExpressions", struct (fun (x0, x1, x2, ()) => .LookupWithDensAndSetupExpressions x0 x1 x2)
      (field "input" <| field "setup" <| field "output" done)),
   ("LookupPairFromBaseInputs", struct (fun (x0, x1, x2, ()) => .LookupPairFromBaseInputs x0 x1 x2)
      (field "input" <| field "output" <| field "range_check_width" done)),
   ("LookupPairFromMaterializedBaseInputs", struct (fun (x0, x1, ()) => .LookupPairFromMaterializedBaseInputs x0 x1)
      (field "input" <| field "output" done)),
   ("LookupFromBaseInputsWithSetup", struct (fun (x0, x1, x2, x3, ()) => .LookupFromBaseInputsWithSetup x0 x1 x2 x3)
      (field "input" <| field "setup" <| field "output" <| field "range_check_width" done)),
   ("LookupFromMaterializedBaseInputWithSetup", struct (fun (x0, x1, x2, ()) => .LookupFromMaterializedBaseInputWithSetup x0 x1 x2)
      (field "input" <| field "setup" <| field "output" done)),
   ("LookupUnbalancedPairWithMaterializedBaseInputs", struct (fun (x0, x1, x2, ()) => .LookupUnbalancedPairWithMaterializedBaseInputs x0 x1 x2)
      (field "input" <| field "remainder" <| field "output" done)),
   ("LookupPairFromVectorInputs", struct (fun (x0, x1, ()) => .LookupPairFromVectorInputs x0 x1)
      (field "input" <| field "output" done)),
   ("LookupPairFromMaterializedVectorInputs", struct (fun (x0, x1, ()) => .LookupPairFromMaterializedVectorInputs x0 x1)
      (field "input" <| field "output" done)),
   ("LookupFromVectorInputWithSetup", struct (fun (x0, x1, x2, ()) => .LookupFromVectorInputWithSetup x0 x1 x2)
      (field "input" <| field "setup" <| field "output" done)),
   ("LookupFromMaterializedVectorInputWithSetup", struct (fun (x0, x1, x2, ()) => .LookupFromMaterializedVectorInputWithSetup x0 x1 x2)
      (field "input" <| field "setup" <| field "output" done)),
   ("LookupPairFromCachedVectorInputs", struct (fun (x0, x1, ()) => .LookupPairFromCachedVectorInputs x0 x1)
      (field "input" <| field "output" done)),
   ("LookupUnbalancedPairWithVectorInputs", struct (fun (x0, x1, x2, ()) => .LookupUnbalancedPairWithVectorInputs x0 x1 x2)
      (field "input" <| field "remainder" <| field "output" done)),
   ("LookupUnbalancedPairWithMaterializedVectorInputs", struct (fun (x0, x1, x2, ()) => .LookupUnbalancedPairWithMaterializedVectorInputs x0 x1 x2)
      (field "input" <| field "remainder" <| field "output" done)),
   ("AggregateLookupRationalPair", struct (fun (x0, x1, ()) => .AggregateLookupRationalPair x0 x1)
      (field "input" <| field "output" done)),
   ("InitsOrTeardownsInitialPair", struct (fun (x0, x1, x2, x3, ()) => .InitsOrTeardownsInitialPair x0 x1 x2 x3)
      (field "timestamp_and_value" <| field "setup" <| field "output" <| field "set_idxes" done))]⟩

instance : Decode GKRCacheRelation := ⟨variants []
  [("SingleColumnLookup", struct (fun (x0, x1, ()) => .SingleColumnLookup x0 x1)
      (field "relation" <| field "range_check_width" done)),
   ("VectorizedLookup", newtype .VectorizedLookup),
   ("MemoryTuple", newtype .MemoryTuple),
   ("VectorizedLookupSetup", newtype .VectorizedLookupSetup)]⟩

instance : Decode GateArtifacts := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "output_layer" <| field "enforced_relation" done)⟩

instance : Decode RamAuxComparisonSet := ⟨struct (fun (x0, ()) => ⟨x0⟩)
  (field "intermediate_borrow" done)⟩

instance : Decode RelativeTimestampGroup := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "read_timestamp" <| field "members" done)⟩

instance : Decode GKRAuxLayoutData := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "shuffle_ram_timestamp_comparison_aux_vars" <| optField "relative_timestamp_groups" done)⟩

instance : Decode GKRLayerDescription := ⟨struct (fun (x0, x1, x2, x3, x4, ()) => ⟨x0, x1, x2, x3, x4⟩)
  (field "layer" <| field "gates_with_external_connections" <| field "cached_relations" <| field "gates" <| field "intermediate_layer_width" done)⟩

instance : Decode RegisterOnlyAccessAddress := ⟨struct (fun (x0, ()) => ⟨x0⟩)
  (field "register_index" done)⟩

instance : Decode RegisterOrRamAddressSpace := ⟨variants []
  [("RegisterAddressSpace", newtype .RegisterAddressSpace),
   ("RamAddressSpace", newtype .RamAddressSpace)]⟩

instance : Decode RegisterOrRamAccessAddress := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "address_space" <| field "address" done)⟩

instance : Decode IndirectRamAccessAddress := ⟨struct (fun (x0, x1, x2, x3, x4, ()) => ⟨x0, x1, x2, x3, x4⟩)
  (field "base_register_value" <| field "base_register_index" <| field "constant_offset" <| field "indirect_access_idx_for_register" <| field "variable_offset" done)⟩

instance : Decode RamAddress := ⟨variants []
  [("ConstantRegister", newtype .ConstantRegister),
   ("RegisterOnly", newtype .RegisterOnly),
   ("RegisterOrRam", newtype .RegisterOrRam),
   ("IndirectRam", newtype .IndirectRam)]⟩

instance : Decode RamReadQuery := ⟨struct (fun (x0, x1, x2, x3, ()) => ⟨x0, x1, x2, x3⟩)
  (field "in_cycle_write_index" <| field "address" <| field "read_timestamp" <| field "read_value" done)⟩

instance : Decode RamWriteQuery := ⟨struct (fun (x0, x1, x2, x3, x4, ()) => ⟨x0, x1, x2, x3, x4⟩)
  (field "in_cycle_write_index" <| field "address" <| field "read_timestamp" <| field "read_value" <| field "write_value" done)⟩

instance : Decode RamQuery := ⟨variants []
  [("Readonly", newtype .Readonly),
   ("Write", newtype .Write)]⟩

instance : Decode GKRMachineState := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "pc" <| field "timestamp" done)⟩

instance : Decode MachineStatePermutationDescription := ⟨struct (fun (x0, x1, x2, ()) => ⟨x0, x1, x2⟩)
  (field "execute" <| field "initial_state" <| field "final_state" done)⟩

instance : Decode CompiledDelegationCircuitState := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "execute" <| field "invocation_timestamp" done)⟩

instance : Decode DecoderPlacementDescription := ⟨struct (fun (x0, x1, x2, x3, x4, x5, x6, ()) => ⟨x0, x1, x2, x3, x4, x5, x6⟩)
  (field "rs1_index" <| field "rs2_index" <| field "rd_index" <| field "circuit_family_mask_bits" <| field "decoder_witness_is_in_memory" <| field "imm" <| field "funct3" done)⟩

instance : Decode GKRMemoryLayout := ⟨struct (fun (x0, x1, x2, x3, x4, x5, x6, x7, ()) => ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩)
  (field "ram_access_sets" <| field "machine_state" <| field "delegation_state" <| field "decoder_input" <| field "indirect_access_variable_offsets" <| field "teardown_sets" <| field "total_width" <| field "inits_and_teardowns_word_bits" done)⟩

instance : Decode GKRWitnessLayout := ⟨struct (fun (x0, x1, x2, x3, ()) => ⟨x0, x1, x2, x3⟩)
  (field "multiplicities_columns_for_range_check_16" <| field "multiplicities_columns_for_timestamp_range_check" <| field "multiplicities_columns_for_generic_lookup" <| field "total_width" done)⟩

instance : Decode Degree1Constraint := ⟨struct (fun (x0, x1, ()) => ⟨x0, x1⟩)
  (field "linear_terms" <| field "constant_term" done)⟩

instance : Decode Degree2Constraint := ⟨struct (fun (x0, x1, x2, ()) => ⟨x0, x1, x2⟩)
  (field "quadratic_terms" <| field "linear_terms" <| field "constant_term" done)⟩

instance : Decode Term := ⟨variants []
  [("Constant", newtype .Constant),
   ("Expression", struct (fun (x0, x1, x2, ()) => .Expression x0 x1 x2)
      (field "coeff" <| field "inner" <| field "degree" done))]⟩

instance : Decode Constraint := ⟨struct (fun (x0, ()) => ⟨x0⟩)
  (field "terms" done)⟩

mutual
def Expr.decode : Value → Except String Expr
  | .obj [(k, p)] =>
    if k = "Constant" then .Constant <$> Decode.decode p
    else if k = "Var" then .Var <$> Decode.decode p
    else if k = "Sum" then .Sum <$> Expr.decodeArray p
    else if k = "Product" then .Product <$> Expr.decodeArray p
    else fail "an Expr variant"
  | _ => fail "an Expr"
def Expr.decodeArray : Value → Except String (Array Expr)
  | .arr vs => List.toArray <$> Expr.decodeList vs
  | _ => fail "an array"
def Expr.decodeList : List Value → Except String (List Expr)
  | [] => .ok []
  | v :: vs => do return (← Expr.decode v) :: (← Expr.decodeList vs)
end

instance : Decode Expr := ⟨Expr.decode⟩

instance : Decode StructuredStatement := ⟨variants []
  [("AssertZero", struct (fun (x0, x1, x2, ()) => .AssertZero x0 x1 x2)
      (field "expr" <| field "compiled_constraint" <| field "prevent_optimizations" done)),
   ("Define", struct (fun (x0, x1, x2, x3, ()) => .Define x0 x1 x2 x3)
      (field "dst" <| field "compiled_constraint" <| field "expr" <| field "output_layer" done))]⟩

instance : Decode GKRCircuitArtifact := ⟨struct (fun (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, ()) => ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26⟩)
  (field "trace_len" <| field "table_offsets" <| field "total_tables_size" <| field "offset_for_decoder_table" <| field "has_decoder_lookup" <| field "layers" <| field "global_output_map" <| field "memory_layout" <| field "witness_layout" <| field "scratch_space_size" <| field "num_generic_lookups" <| field "placement_data" <| field "generic_lookup_tables_width" <| field "decode_table_columns_mask" <| field "tables_ids_in_generic_lookups" <| optField "generic_lookup_padding" <| field "degree_2_constraints" <| field "degree_1_constraints" <| field "structured_statements" <| field "generic_lookups" <| field "range_check_16_lookup_expressions" <| field "timestamp_range_check_lookup_expressions" <| field "variable_names" <| field "scratch_space_mapping" <| field "scratch_space_mapping_rev" <| field "aux_layout_data" <| field "_marker" done)⟩

end Decode

/-- The circuit artifact of a JSON value. -/
def Circuit.decode : Json.Value → Except String Circuit := Decode.decode

end Airbender
