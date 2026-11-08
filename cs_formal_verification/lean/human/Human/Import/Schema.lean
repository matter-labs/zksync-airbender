module
public import Human.Import.Serde

@[expose] public section

/- Native mirror of the v3 Rust serde schema at commit 28ffe3ff0353edd9051485c2974b28b52b495dc4.
   Coefficients are fixed to BabyBear Montgomery encoding. No fields are opaque JSON. -/
namespace Airbender
open Serde (encode)
open Json (tag omitNone)

structure ColumnRange where
  start : Nat
  «end» : Nat
  deriving Repr

instance : Serde ColumnRange := ⟨fun r => .obj [("start", encode r.start), ("end", encode r.«end»)]⟩

/-- Source: `cs/src/definitions/gkr_layers.rs`, `OutputType`. -/
inductive OutputType where
  | PermutationProduct
  | Lookup16Bits
  | LookupTimestamps
  | GenericLookup
  | InitsAndTeardownsProduct
  deriving Repr

instance : ObjectKey OutputType := ⟨fun
  | .PermutationProduct => "PermutationProduct" | .Lookup16Bits => "Lookup16Bits"
  | .LookupTimestamps => "LookupTimestamps" | .GenericLookup => "GenericLookup"
  | .InitsAndTeardownsProduct => "InitsAndTeardownsProduct"⟩

/-- Source: `cs/src/definitions/gkr_layers.rs`, `VirtualSetupPoly`. -/
inductive VirtualSetupPoly where
  | RangeCheck16Bits
  | RangeCheckTimestamp
  | InitsAndTeardownsLow
  | InitsAndTeardownsHigh
  deriving Repr, DecidableEq

instance : Serde VirtualSetupPoly := ⟨fun
  | .RangeCheck16Bits => .str "RangeCheck16Bits" | .RangeCheckTimestamp => .str "RangeCheckTimestamp"
  | .InitsAndTeardownsLow => .str "InitsAndTeardownsLow" | .InitsAndTeardownsHigh => .str "InitsAndTeardownsHigh"⟩

/-- Source: `cs/src/definitions/gkr_layers.rs`, `GKRAddress`. -/
inductive GKRAddress where
  | BaseLayerWitness : Nat → GKRAddress
  | BaseLayerMemory : Nat → GKRAddress
  | InnerLayer (layer : Nat) (offset : Nat)
  | Setup : Nat → GKRAddress
  | VirtualSetup : VirtualSetupPoly → GKRAddress
  | ScratchSpace : Nat → GKRAddress
  | Cached (layer : Nat) (offset : Nat)
  deriving Repr, DecidableEq

instance : Serde GKRAddress := ⟨fun
  | .BaseLayerWitness i => tag "BaseLayerWitness" (encode i)
  | .BaseLayerMemory i => tag "BaseLayerMemory" (encode i)
  | .InnerLayer layer offset => tag "InnerLayer" (.obj [("layer", encode layer), ("offset", encode offset)])
  | .Setup i => tag "Setup" (encode i)
  | .VirtualSetup p => tag "VirtualSetup" (encode p)
  | .ScratchSpace i => tag "ScratchSpace" (encode i)
  | .Cached layer offset => tag "Cached" (.obj [("layer", encode layer), ("offset", encode offset)])⟩

/-- Source: `cs/src/definitions/gkr/utils.rs`, `LinearRelation`. -/
structure LinearRelation where
  linear_terms : (Array (Coefficient × GKRAddress))
  constant : Coefficient
  deriving Repr

instance : Serde LinearRelation := ⟨fun r => .obj [
  ("linear_terms", encode r.linear_terms), ("constant", encode r.constant)]⟩

/-- Source: `cs/src/definitions/gkr/lookup.rs`, `SingleColumnLookupRelation`. -/
structure SingleColumnLookupRelation where
  input : LinearRelation
  lookup_set_index : Nat
  deriving Repr

instance : Serde SingleColumnLookupRelation := ⟨fun r => .obj [
  ("input", encode r.input), ("lookup_set_index", encode r.lookup_set_index)]⟩

/-- Source: `cs/src/definitions/gkr/lookup.rs`, `VectorLookupRelation`. -/
structure VectorLookupRelation where
  columns : (Array LinearRelation)
  lookup_set_index : Nat
  deriving Repr

instance : Serde VectorLookupRelation := ⟨fun r => .obj [
  ("columns", encode r.columns), ("lookup_set_index", encode r.lookup_set_index)]⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `CompiledMaxQuadraticGKRRelation`. -/
structure CompiledMaxQuadraticGKRRelation where
  quadratic_terms : (Array (GKRAddress × (Array (Coefficient × GKRAddress))))
  linear_terms : (Array (Coefficient × GKRAddress))
  constant : Coefficient
  deriving Repr

instance : Serde CompiledMaxQuadraticGKRRelation := ⟨fun r => .obj [
  ("quadratic_terms", encode r.quadratic_terms), ("linear_terms", encode r.linear_terms),
  ("constant", encode r.constant)]⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `CompiledAddressSpaceRelationStrict`. -/
inductive CompiledAddressSpaceRelationStrict where
  | Constant : U32 → CompiledAddressSpaceRelationStrict
  | IsRegister : Nat → CompiledAddressSpaceRelationStrict
  | IsRam : Nat → CompiledAddressSpaceRelationStrict
  deriving Repr

instance : Serde CompiledAddressSpaceRelationStrict := ⟨fun
  | .Constant c => tag "Constant" (encode c) | .IsRegister i => tag "IsRegister" (encode i)
  | .IsRam i => tag "IsRam" (encode i)⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `CompiledAddressStrict`. -/
inductive CompiledAddressStrict where
  | ConstantU16 : U16 → CompiledAddressStrict
  | Constant : U32 → CompiledAddressStrict
  | U16Space : Nat → CompiledAddressStrict
  | U32Space : (Fixed 2 Nat) → CompiledAddressStrict
  | U32SpaceSpecialIndirect (low_base : Nat) (low_dynamic_offset : (Option (U16 × Nat))) (low_offset : U32) (high : Nat)
  | U32SpaceGeneric : (Fixed 2 ((Array ((BoundedNat 18446744073709551616) × Nat)) × (BoundedNat 18446744073709551616))) → CompiledAddressStrict
  deriving Repr

instance : Serde CompiledAddressStrict := ⟨fun
  | .ConstantU16 c => tag "ConstantU16" (encode c)
  | .Constant c => tag "Constant" (encode c)
  | .U16Space i => tag "U16Space" (encode i)
  | .U32Space i => tag "U32Space" (encode i)
  | .U32SpaceSpecialIndirect low_base low_dynamic_offset low_offset high => tag "U32SpaceSpecialIndirect" (.obj
      [("low_base", encode low_base), ("low_dynamic_offset", encode low_dynamic_offset),
       ("low_offset", encode low_offset), ("high", encode high)])
  | .U32SpaceGeneric g => tag "U32SpaceGeneric" (encode g)⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `CompiledMemoryTimestamp`. -/
inductive CompiledMemoryTimestamp where
  | Zero
  | Normal : (Fixed 2 Nat) → CompiledMemoryTimestamp
  deriving Repr

instance : Serde CompiledMemoryTimestamp := ⟨fun
  | .Zero => .str "Zero" | .Normal t => tag "Normal" (encode t)⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamWordRepresentation`. -/
inductive RamWordRepresentation where
  | Zero
  | U16Limbs : (Fixed 2 Nat) → RamWordRepresentation
  | U8Limbs : (Fixed 4 Nat) → RamWordRepresentation
  deriving Repr

instance : Serde RamWordRepresentation := ⟨fun
  | .Zero => .str "Zero" | .U16Limbs l => tag "U16Limbs" (encode l) | .U8Limbs l => tag "U8Limbs" (encode l)⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `SpecialMemoryContributionRelation`. -/
structure SpecialMemoryContributionRelation where
  address_space : CompiledAddressSpaceRelationStrict
  address : CompiledAddressStrict
  timestamp : CompiledMemoryTimestamp
  value : RamWordRepresentation
  timestamp_offset : U32
  deriving Repr

instance : Serde SpecialMemoryContributionRelation := ⟨fun r => .obj [("address_space", encode r.address_space),
  ("address", encode r.address), ("timestamp", encode r.timestamp), ("value", encode r.value),
  ("timestamp_offset", encode r.timestamp_offset)]⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `MaxQuadraticConstraintsGKRRelation`. -/
structure MaxQuadraticConstraintsGKRRelation where
  quadratic_terms : (Array ((GKRAddress × GKRAddress) × (Array (Coefficient × Nat))))
  linear_terms : (Array (GKRAddress × (Array (Coefficient × Nat))))
  constants : (Array (Coefficient × Nat))
  deriving Repr

instance : Serde MaxQuadraticConstraintsGKRRelation := ⟨fun r => .obj [
  ("quadratic_terms", encode r.quadratic_terms), ("linear_terms", encode r.linear_terms),
  ("constants", encode r.constants)]⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `InitsOrTeardownsTimestampAndValue`. -/
inductive InitsOrTeardownsTimestampAndValue where
  | Init
  | Teardown (lhs_timestamp : (Fixed 2 Nat)) (lhs_value : (Fixed 2 Nat)) (rhs_timestamp : (Fixed 2 Nat)) (rhs_value : (Fixed 2 Nat))
  deriving Repr

instance : Serde InitsOrTeardownsTimestampAndValue := ⟨fun
  | .Init => .str "Init"
  | .Teardown lhs_timestamp lhs_value rhs_timestamp rhs_value => tag "Teardown" (.obj
      [("lhs_timestamp", encode lhs_timestamp), ("lhs_value", encode lhs_value),
       ("rhs_timestamp", encode rhs_timestamp), ("rhs_value", encode rhs_value)])⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `StructuredExpression`. -/
inductive StructuredExpression where
  | Constant : Coefficient → StructuredExpression
  | Place : GKRAddress → StructuredExpression
  | Sum : (Array StructuredExpression) → StructuredExpression
  | Product : (Array StructuredExpression) → StructuredExpression
  deriving Repr

def StructuredExpression.encode : StructuredExpression → Json.Value
  | .Constant c => tag "Constant" (Serde.encode c)
  | .Place a => tag "Place" (Serde.encode a)
  | .Sum ⟨xs⟩ => tag "Sum" (.arr (xs.map StructuredExpression.encode))
  | .Product ⟨xs⟩ => tag "Product" (.arr (xs.map StructuredExpression.encode))

instance : Serde StructuredExpression := ⟨StructuredExpression.encode⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `GKRRelation`. -/
inductive GKRRelation where
  | LinearBaseFieldRelation (input : LinearRelation) (output : GKRAddress)
  | MaxQuadratic (input : CompiledMaxQuadraticGKRRelation) (expression : StructuredExpression) (output : GKRAddress)
  | EnforceSingleMaxQuadraticConstraint (input : CompiledMaxQuadraticGKRRelation) (expression : StructuredExpression)
  | EnforceConstraintsMaxQuadratic (input : MaxQuadraticConstraintsGKRRelation)
  | CopyInBaseField (input : GKRAddress) (output : GKRAddress)
  | CopyInExtensionField (input : GKRAddress) (output : GKRAddress)
  | InitialGrandProductFromCaches (input : (Fixed 2 GKRAddress)) (output : GKRAddress)
  | InitialGrandProductWithoutCaches (input : (Fixed 2 SpecialMemoryContributionRelation)) (output : GKRAddress)
  | UnbalancedGrandProductWithCache (scalar : GKRAddress) (input : GKRAddress) (output : GKRAddress)
  | MaterializeGrandProductTermExpression (input : SpecialMemoryContributionRelation) (output : GKRAddress)
  | TrivialProduct (input : (Fixed 2 GKRAddress)) (output : GKRAddress)
  | MaskIntoIdentityProduct (input : GKRAddress) (mask : GKRAddress) (output : GKRAddress)
  | MaterializeSingleLookupInput (input : SingleColumnLookupRelation) (output : GKRAddress) (range_check_width : U32)
  | MaterializedVectorLookupInput (input : VectorLookupRelation) (output : GKRAddress)
  | LookupWithCachedDensAndSetup (input : (Fixed 2 GKRAddress)) (setup : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupWithDensAndSetupExpressions (input : (GKRAddress × VectorLookupRelation)) (setup : (GKRAddress × (Array GKRAddress))) (output : (Fixed 2 GKRAddress))
  | LookupPairFromBaseInputs (input : (Fixed 2 SingleColumnLookupRelation)) (output : (Fixed 2 GKRAddress)) (range_check_width : U32)
  | LookupPairFromMaterializedBaseInputs (input : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupFromBaseInputsWithSetup (input : SingleColumnLookupRelation) (setup : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress)) (range_check_width : U32)
  | LookupFromMaterializedBaseInputWithSetup (input : GKRAddress) (setup : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupUnbalancedPairWithMaterializedBaseInputs (input : (Fixed 2 GKRAddress)) (remainder : GKRAddress) (output : (Fixed 2 GKRAddress))
  | LookupPairFromVectorInputs (input : (Fixed 2 VectorLookupRelation)) (output : (Fixed 2 GKRAddress))
  | LookupPairFromMaterializedVectorInputs (input : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupFromVectorInputWithSetup (input : VectorLookupRelation) (setup : (GKRAddress × (Array GKRAddress))) (output : (Fixed 2 GKRAddress))
  | LookupFromMaterializedVectorInputWithSetup (input : GKRAddress) (setup : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupPairFromCachedVectorInputs (input : (Fixed 2 GKRAddress)) (output : (Fixed 2 GKRAddress))
  | LookupUnbalancedPairWithVectorInputs (input : (Fixed 2 GKRAddress)) (remainder : VectorLookupRelation) (output : (Fixed 2 GKRAddress))
  | LookupUnbalancedPairWithMaterializedVectorInputs (input : (Fixed 2 GKRAddress)) (remainder : GKRAddress) (output : (Fixed 2 GKRAddress))
  | AggregateLookupRationalPair (input : (Fixed 2 (Fixed 2 GKRAddress))) (output : (Fixed 2 GKRAddress))
  | InitsOrTeardownsInitialPair (timestamp_and_value : InitsOrTeardownsTimestampAndValue) (setup : (Fixed 2 GKRAddress)) (output : GKRAddress) (set_idxes : (Fixed 2 Nat))
  deriving Repr

instance : Serde GKRRelation := ⟨fun
  | .LinearBaseFieldRelation input output =>
      tag "LinearBaseFieldRelation" (.obj [("input", encode input), ("output", encode output)])
  | .MaxQuadratic input expression output =>
      tag "MaxQuadratic" (.obj [
        ("input", encode input), ("expression", encode expression), ("output", encode output)])
  | .EnforceSingleMaxQuadraticConstraint input expression =>
      tag "EnforceSingleMaxQuadraticConstraint" (.obj [("input", encode input), ("expression", encode expression)])
  | .EnforceConstraintsMaxQuadratic input => tag "EnforceConstraintsMaxQuadratic" (.obj [("input", encode input)])
  | .CopyInBaseField input output => tag "CopyInBaseField" (.obj [("input", encode input), ("output", encode output)])
  | .CopyInExtensionField input output =>
      tag "CopyInExtensionField" (.obj [("input", encode input), ("output", encode output)])
  | .InitialGrandProductFromCaches input output =>
      tag "InitialGrandProductFromCaches" (.obj [("input", encode input), ("output", encode output)])
  | .InitialGrandProductWithoutCaches input output =>
      tag "InitialGrandProductWithoutCaches" (.obj [("input", encode input), ("output", encode output)])
  | .UnbalancedGrandProductWithCache scalar input output =>
      tag "UnbalancedGrandProductWithCache" (.obj [
        ("scalar", encode scalar), ("input", encode input), ("output", encode output)])
  | .MaterializeGrandProductTermExpression input output =>
      tag "MaterializeGrandProductTermExpression" (.obj [("input", encode input), ("output", encode output)])
  | .TrivialProduct input output => tag "TrivialProduct" (.obj [("input", encode input), ("output", encode output)])
  | .MaskIntoIdentityProduct input mask output =>
      tag "MaskIntoIdentityProduct" (.obj [("input", encode input), ("mask", encode mask), ("output", encode output)])
  | .MaterializeSingleLookupInput input output range_check_width =>
      tag "MaterializeSingleLookupInput" (.obj [
        ("input", encode input), ("output", encode output), ("range_check_width", encode range_check_width)])
  | .MaterializedVectorLookupInput input output =>
      tag "MaterializedVectorLookupInput" (.obj [("input", encode input), ("output", encode output)])
  | .LookupWithCachedDensAndSetup input setup output =>
      tag "LookupWithCachedDensAndSetup" (.obj [
        ("input", encode input), ("setup", encode setup), ("output", encode output)])
  | .LookupWithDensAndSetupExpressions input setup output =>
      tag "LookupWithDensAndSetupExpressions" (.obj [
        ("input", encode input), ("setup", encode setup), ("output", encode output)])
  | .LookupPairFromBaseInputs input output range_check_width =>
      tag "LookupPairFromBaseInputs" (.obj [
        ("input", encode input), ("output", encode output), ("range_check_width", encode range_check_width)])
  | .LookupPairFromMaterializedBaseInputs input output =>
      tag "LookupPairFromMaterializedBaseInputs" (.obj [("input", encode input), ("output", encode output)])
  | .LookupFromBaseInputsWithSetup input setup output range_check_width =>
      tag "LookupFromBaseInputsWithSetup" (.obj [
        ("input", encode input), ("setup", encode setup), ("output", encode output),
        ("range_check_width", encode range_check_width)])
  | .LookupFromMaterializedBaseInputWithSetup input setup output =>
      tag "LookupFromMaterializedBaseInputWithSetup" (.obj [
        ("input", encode input), ("setup", encode setup), ("output", encode output)])
  | .LookupUnbalancedPairWithMaterializedBaseInputs input remainder output =>
      tag "LookupUnbalancedPairWithMaterializedBaseInputs" (.obj [
        ("input", encode input), ("remainder", encode remainder), ("output", encode output)])
  | .LookupPairFromVectorInputs input output =>
      tag "LookupPairFromVectorInputs" (.obj [("input", encode input), ("output", encode output)])
  | .LookupPairFromMaterializedVectorInputs input output =>
      tag "LookupPairFromMaterializedVectorInputs" (.obj [("input", encode input), ("output", encode output)])
  | .LookupFromVectorInputWithSetup input setup output =>
      tag "LookupFromVectorInputWithSetup" (.obj [
        ("input", encode input), ("setup", encode setup), ("output", encode output)])
  | .LookupFromMaterializedVectorInputWithSetup input setup output =>
      tag "LookupFromMaterializedVectorInputWithSetup" (.obj [
        ("input", encode input), ("setup", encode setup), ("output", encode output)])
  | .LookupPairFromCachedVectorInputs input output =>
      tag "LookupPairFromCachedVectorInputs" (.obj [("input", encode input), ("output", encode output)])
  | .LookupUnbalancedPairWithVectorInputs input remainder output =>
      tag "LookupUnbalancedPairWithVectorInputs" (.obj [
        ("input", encode input), ("remainder", encode remainder), ("output", encode output)])
  | .LookupUnbalancedPairWithMaterializedVectorInputs input remainder output =>
      tag "LookupUnbalancedPairWithMaterializedVectorInputs" (.obj [
        ("input", encode input), ("remainder", encode remainder), ("output", encode output)])
  | .AggregateLookupRationalPair input output =>
      tag "AggregateLookupRationalPair" (.obj [("input", encode input), ("output", encode output)])
  | .InitsOrTeardownsInitialPair timestamp_and_value setup output set_idxes =>
      tag "InitsOrTeardownsInitialPair" (.obj [
        ("timestamp_and_value", encode timestamp_and_value), ("setup", encode setup), ("output", encode output),
        ("set_idxes", encode set_idxes)])⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `GKRCacheRelation`. -/
inductive GKRCacheRelation where
  | SingleColumnLookup (relation : SingleColumnLookupRelation) (range_check_width : Nat)
  | VectorizedLookup : VectorLookupRelation → GKRCacheRelation
  | MemoryTuple : SpecialMemoryContributionRelation → GKRCacheRelation
  | VectorizedLookupSetup : (Array GKRAddress) → GKRCacheRelation
  deriving Repr

instance : Serde GKRCacheRelation := ⟨fun
  | .SingleColumnLookup relation range_check_width => tag "SingleColumnLookup"
      (.obj [("relation", encode relation), ("range_check_width", encode range_check_width)])
  | .VectorizedLookup r => tag "VectorizedLookup" (encode r)
  | .MemoryTuple r => tag "MemoryTuple" (encode r)
  | .VectorizedLookupSetup r => tag "VectorizedLookupSetup" (encode r)⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `GateArtifacts`. -/
structure GateArtifacts where
  output_layer : Nat
  enforced_relation : GKRRelation
  deriving Repr

instance : Serde GateArtifacts := ⟨fun g => .obj [
  ("output_layer", encode g.output_layer), ("enforced_relation", encode g.enforced_relation)]⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamAuxComparisonSet`. -/
structure RamAuxComparisonSet where
  intermediate_borrow : GKRAddress
  deriving Repr

instance : Serde RamAuxComparisonSet := ⟨fun s => .obj [("intermediate_borrow", encode s.intermediate_borrow)]⟩

/-- One shared read timestamp of the split Keccak workers: `members` index the
    memory ports that read at that time. Source: `cs/src/gkr_compiler/layout.rs`. -/
structure RelativeTimestampGroup where
  read_timestamp : Fixed 2 Nat
  members : Array Nat
  deriving Repr

instance : Serde RelativeTimestampGroup := ⟨fun g => .obj [
  ("read_timestamp", encode g.read_timestamp), ("members", encode g.members)]⟩

/-- Source: `cs/src/gkr_compiler/layout.rs`, `GKRAuxLayoutData`. Split workers
    with grouped timestamps have no per-port borrow (`null` entries). -/
structure GKRAuxLayoutData where
  shuffle_ram_timestamp_comparison_aux_vars : Array (Option RamAuxComparisonSet)
  relative_timestamp_groups : Option (Array RelativeTimestampGroup) := none
  deriving Repr

instance : Serde GKRAuxLayoutData := ⟨fun d => .obj
  ([("shuffle_ram_timestamp_comparison_aux_vars", encode d.shuffle_ram_timestamp_comparison_aux_vars)] ++
    omitNone "relative_timestamp_groups" d.relative_timestamp_groups)⟩

/-- Source: `cs/src/gkr_compiler/layout.rs`, `GKRLayerDescription`. -/
structure GKRLayerDescription where
  layer : Nat
  gates_with_external_connections : (Array GateArtifacts)
  cached_relations : (Array (GKRAddress × GKRCacheRelation))
  gates : (Array GateArtifacts)
  intermediate_layer_width : (Option Nat)
  deriving Repr

instance : Serde GKRLayerDescription := ⟨fun l => .obj [("layer", encode l.layer),
  ("gates_with_external_connections", encode l.gates_with_external_connections),
  ("cached_relations", encode l.cached_relations), ("gates", encode l.gates),
  ("intermediate_layer_width", encode l.intermediate_layer_width)]⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RegisterOnlyAccessAddress`. -/
structure RegisterOnlyAccessAddress where
  register_index : Nat
  deriving Repr

instance : Serde RegisterOnlyAccessAddress := ⟨fun a => .obj [("register_index", encode a.register_index)]⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RegisterOrRamAddressSpace`. -/
inductive RegisterOrRamAddressSpace where
  | RegisterAddressSpace : Nat → RegisterOrRamAddressSpace
  | RamAddressSpace : Nat → RegisterOrRamAddressSpace
  deriving Repr

instance : Serde RegisterOrRamAddressSpace := ⟨fun
  | .RegisterAddressSpace i => tag "RegisterAddressSpace" (encode i)
  | .RamAddressSpace i => tag "RamAddressSpace" (encode i)⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RegisterOrRamAccessAddress`. -/
structure RegisterOrRamAccessAddress where
  address_space : RegisterOrRamAddressSpace
  address : (Fixed 2 Nat)
  deriving Repr

instance : Serde RegisterOrRamAccessAddress := ⟨fun a => .obj [
  ("address_space", encode a.address_space), ("address", encode a.address)]⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `IndirectRamAccessAddress`. -/
structure IndirectRamAccessAddress where
  base_register_value : (Fixed 2 Nat)
  base_register_index : U16
  constant_offset : U16
  indirect_access_idx_for_register : Nat
  variable_offset : (Option (U16 × Nat))
  deriving Repr

instance : Serde IndirectRamAccessAddress := ⟨fun a => .obj [("base_register_value", encode a.base_register_value),
  ("base_register_index", encode a.base_register_index), ("constant_offset", encode a.constant_offset),
  ("indirect_access_idx_for_register", encode a.indirect_access_idx_for_register),
  ("variable_offset", encode a.variable_offset)]⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamAddress`. -/
inductive RamAddress where
  | ConstantRegister : U16 → RamAddress
  | RegisterOnly : RegisterOnlyAccessAddress → RamAddress
  | RegisterOrRam : RegisterOrRamAccessAddress → RamAddress
  | IndirectRam : IndirectRamAccessAddress → RamAddress
  deriving Repr

instance : Serde RamAddress := ⟨fun
  | .ConstantRegister r => tag "ConstantRegister" (encode r) | .RegisterOnly a => tag "RegisterOnly" (encode a)
  | .RegisterOrRam a => tag "RegisterOrRam" (encode a) | .IndirectRam a => tag "IndirectRam" (encode a)⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamReadQuery`. -/
structure RamReadQuery where
  in_cycle_write_index : U32
  address : RamAddress
  read_timestamp : (Fixed 2 Nat)
  read_value : RamWordRepresentation
  deriving Repr

instance : Serde RamReadQuery := ⟨fun q => .obj [("in_cycle_write_index", encode q.in_cycle_write_index),
  ("address", encode q.address), ("read_timestamp", encode q.read_timestamp), ("read_value", encode q.read_value)]⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamWriteQuery`. -/
structure RamWriteQuery where
  in_cycle_write_index : U32
  address : RamAddress
  read_timestamp : (Fixed 2 Nat)
  read_value : RamWordRepresentation
  write_value : RamWordRepresentation
  deriving Repr

instance : Serde RamWriteQuery := ⟨fun q => .obj [("in_cycle_write_index", encode q.in_cycle_write_index),
  ("address", encode q.address), ("read_timestamp", encode q.read_timestamp), ("read_value", encode q.read_value),
  ("write_value", encode q.write_value)]⟩

/-- Source: `cs/src/definitions/gkr/ram_access.rs`, `RamQuery`. -/
inductive RamQuery where
  | Readonly : RamReadQuery → RamQuery
  | Write : RamWriteQuery → RamQuery
  deriving Repr

instance : Serde RamQuery := ⟨fun
  | .Readonly q => tag "Readonly" (encode q) | .Write q => tag "Write" (encode q)⟩

/-- Source: `cs/src/definitions/gkr/mod.rs`, `GKRMachineState`. -/
structure GKRMachineState where
  pc : (Fixed 2 Nat)
  timestamp : (Fixed 2 Nat)
  deriving Repr

instance : Serde GKRMachineState := ⟨fun s => .obj [("pc", encode s.pc), ("timestamp", encode s.timestamp)]⟩

/-- Source: `cs/src/definitions/gkr/mod.rs`, `MachineStatePermutationDescription`. -/
structure MachineStatePermutationDescription where
  execute : Nat
  initial_state : GKRMachineState
  final_state : GKRMachineState
  deriving Repr

instance : Serde MachineStatePermutationDescription := ⟨fun d => .obj [("execute", encode d.execute),
  ("initial_state", encode d.initial_state), ("final_state", encode d.final_state)]⟩

/-- Source: `cs/src/definitions/gkr/mod.rs`, `CompiledDelegationCircuitState`. -/
structure CompiledDelegationCircuitState where
  execute : Nat
  invocation_timestamp : (Fixed 2 Nat)
  deriving Repr

instance : Serde CompiledDelegationCircuitState := ⟨fun s => .obj [
  ("execute", encode s.execute), ("invocation_timestamp", encode s.invocation_timestamp)]⟩

/-- Source: `cs/src/definitions/gkr/mod.rs`, `DecoderPlacementDescription`. -/
structure DecoderPlacementDescription where
  rs1_index : Nat
  rs2_index : GKRAddress
  rd_index : GKRAddress
  circuit_family_mask_bits : (Array GKRAddress)
  decoder_witness_is_in_memory : Bool
  imm : (Fixed 2 Nat)
  funct3 : (Option Nat)
  deriving Repr

instance : Serde DecoderPlacementDescription := ⟨fun d => .obj [("rs1_index", encode d.rs1_index),
  ("rs2_index", encode d.rs2_index), ("rd_index", encode d.rd_index),
  ("circuit_family_mask_bits", encode d.circuit_family_mask_bits),
  ("decoder_witness_is_in_memory", encode d.decoder_witness_is_in_memory), ("imm", encode d.imm),
  ("funct3", encode d.funct3)]⟩

/-- Source: `cs/src/definitions/gkr/mod.rs`, `GKRMemoryLayout`. -/
structure GKRMemoryLayout where
  ram_access_sets : (Array RamQuery)
  machine_state : (Option MachineStatePermutationDescription)
  delegation_state : (Option CompiledDelegationCircuitState)
  decoder_input : (Option DecoderPlacementDescription)
  indirect_access_variable_offsets : (Array Nat)
  teardown_sets : (Array ((Fixed 2 GKRAddress) × (Fixed 2 GKRAddress)))
  total_width : Nat
  inits_and_teardowns_word_bits : (Option U32)
  deriving Repr

instance : Serde GKRMemoryLayout := ⟨fun l => .obj [("ram_access_sets", encode l.ram_access_sets),
  ("machine_state", encode l.machine_state), ("delegation_state", encode l.delegation_state),
  ("decoder_input", encode l.decoder_input),
  ("indirect_access_variable_offsets", encode l.indirect_access_variable_offsets),
  ("teardown_sets", encode l.teardown_sets), ("total_width", encode l.total_width),
  ("inits_and_teardowns_word_bits", encode l.inits_and_teardowns_word_bits)]⟩

/-- Source: `cs/src/definitions/gkr/mod.rs`, `GKRWitnessLayout`. -/
structure GKRWitnessLayout where
  multiplicities_columns_for_range_check_16 : ColumnRange
  multiplicities_columns_for_timestamp_range_check : ColumnRange
  multiplicities_columns_for_generic_lookup : ColumnRange
  total_width : Nat
  deriving Repr

instance : Serde GKRWitnessLayout := ⟨fun l => .obj [
  ("multiplicities_columns_for_range_check_16", encode l.multiplicities_columns_for_range_check_16),
  ("multiplicities_columns_for_timestamp_range_check", encode l.multiplicities_columns_for_timestamp_range_check),
  ("multiplicities_columns_for_generic_lookup", encode l.multiplicities_columns_for_generic_lookup),
  ("total_width", encode l.total_width)]⟩

/-- Source: `cs/src/definitions/constraints.rs`, `Degree1Constraint`. -/
structure Degree1Constraint where
  linear_terms : (Array (Coefficient × Nat))
  constant_term : Coefficient
  deriving Repr

instance : Serde Degree1Constraint := ⟨fun c => .obj [
  ("linear_terms", encode c.linear_terms), ("constant_term", encode c.constant_term)]⟩

/-- Source: `cs/src/definitions/constraints.rs`, `Degree2Constraint`. -/
structure Degree2Constraint where
  quadratic_terms : (Array (Triple Coefficient Nat Nat))
  linear_terms : (Array (Coefficient × Nat))
  constant_term : Coefficient
  deriving Repr

instance : Serde Degree2Constraint := ⟨fun c => .obj [("quadratic_terms", encode c.quadratic_terms),
  ("linear_terms", encode c.linear_terms), ("constant_term", encode c.constant_term)]⟩

/-- Source: `cs/src/constraint.rs`, `Term`. -/
inductive Term where
  | Constant : Coefficient → Term
  | Expression (coeff : Coefficient) (inner : (Fixed 4 Nat)) (degree : Nat)
  deriving Repr

instance : Serde Term := ⟨fun
  | .Constant c => tag "Constant" (encode c)
  | .Expression coeff inner degree =>
      tag "Expression" (.obj [("coeff", encode coeff), ("inner", encode inner), ("degree", encode degree)])⟩

/-- Source: `cs/src/constraint.rs`, `Constraint`. -/
structure Constraint where
  terms : (Array Term)
  deriving Repr

instance : Serde Constraint := ⟨fun c => .obj [("terms", encode c.terms)]⟩

/-- Source: `cs/src/structured_expr.rs`, `Expr`. -/
inductive Expr where
  | Constant : Coefficient → Expr
  | Var : Nat → Expr
  | Sum : (Array Expr) → Expr
  | Product : (Array Expr) → Expr
  deriving Repr

def Expr.encode : Expr → Json.Value
  | .Constant c => tag "Constant" (Serde.encode c)
  | .Var v => tag "Var" (Serde.encode v)
  | .Sum ⟨xs⟩ => tag "Sum" (.arr (xs.map Expr.encode))
  | .Product ⟨xs⟩ => tag "Product" (.arr (xs.map Expr.encode))

instance : Serde Expr := ⟨Expr.encode⟩

/-- Source: `cs/src/structured_expr.rs`, `StructuredStatement`. -/
inductive StructuredStatement where
  | AssertZero (expr : Expr) (compiled_constraint : Constraint) (prevent_optimizations : Bool)
  | Define (dst : Nat) (compiled_constraint : Constraint) (expr : Expr) (output_layer : Nat)
  deriving Repr

instance : Serde StructuredStatement := ⟨fun
  | .AssertZero expr compiled_constraint prevent_optimizations => tag "AssertZero" (.obj [("expr", encode expr),
      ("compiled_constraint", encode compiled_constraint), ("prevent_optimizations", encode prevent_optimizations)])
  | .Define dst compiled_constraint expr output_layer => tag "Define" (.obj [("dst", encode dst),
      ("compiled_constraint", encode compiled_constraint), ("expr", encode expr),
      ("output_layer", encode output_layer)])⟩

/-- Source: `cs/src/gkr_compiler/mod.rs`, `GKRCircuitArtifact`. -/
structure GKRCircuitArtifact where
  trace_len : Nat
  table_offsets : (Array U32)
  total_tables_size : Nat
  offset_for_decoder_table : Nat
  has_decoder_lookup : Bool
  layers : (Array GKRLayerDescription)
  global_output_map : (ObjectMap OutputType (Array GKRAddress))
  memory_layout : GKRMemoryLayout
  witness_layout : GKRWitnessLayout
  scratch_space_size : Nat
  num_generic_lookups : Nat
  placement_data : (ObjectMap Nat GKRAddress)
  generic_lookup_tables_width : Nat
  decode_table_columns_mask : (Array Bool)
  tables_ids_in_generic_lookups : Bool
  generic_lookup_padding : Option Coefficient := none
  degree_2_constraints : (Array Degree2Constraint)
  degree_1_constraints : (Array Degree1Constraint)
  structured_statements : (Array StructuredStatement)
  generic_lookups : (Array VectorLookupRelation)
  range_check_16_lookup_expressions : (Array SingleColumnLookupRelation)
  timestamp_range_check_lookup_expressions : (Array SingleColumnLookupRelation)
  variable_names : (ObjectMap Nat String)
  scratch_space_mapping : (Array (GKRAddress × Nat))
  scratch_space_mapping_rev : (ObjectMap Nat GKRAddress)
  aux_layout_data : GKRAuxLayoutData
  _marker : JsonNull
  deriving Repr

instance : Serde GKRCircuitArtifact := ⟨fun c => .obj (
  [("trace_len", encode c.trace_len), ("table_offsets", encode c.table_offsets),
   ("total_tables_size", encode c.total_tables_size),
   ("offset_for_decoder_table", encode c.offset_for_decoder_table),
   ("has_decoder_lookup", encode c.has_decoder_lookup), ("layers", encode c.layers),
   ("global_output_map", encode c.global_output_map), ("memory_layout", encode c.memory_layout),
   ("witness_layout", encode c.witness_layout), ("scratch_space_size", encode c.scratch_space_size),
   ("num_generic_lookups", encode c.num_generic_lookups), ("placement_data", encode c.placement_data),
   ("generic_lookup_tables_width", encode c.generic_lookup_tables_width),
   ("decode_table_columns_mask", encode c.decode_table_columns_mask),
   ("tables_ids_in_generic_lookups", encode c.tables_ids_in_generic_lookups)] ++
  omitNone "generic_lookup_padding" c.generic_lookup_padding ++
  [("degree_2_constraints", encode c.degree_2_constraints), ("degree_1_constraints", encode c.degree_1_constraints),
   ("structured_statements", encode c.structured_statements), ("generic_lookups", encode c.generic_lookups),
   ("range_check_16_lookup_expressions", encode c.range_check_16_lookup_expressions),
   ("timestamp_range_check_lookup_expressions", encode c.timestamp_range_check_lookup_expressions),
   ("variable_names", encode c.variable_names), ("scratch_space_mapping", encode c.scratch_space_mapping),
   ("scratch_space_mapping_rev", encode c.scratch_space_mapping_rev), ("aux_layout_data", encode c.aux_layout_data),
   ("_marker", encode c._marker)])⟩

abbrev Circuit := GKRCircuitArtifact

end Airbender
