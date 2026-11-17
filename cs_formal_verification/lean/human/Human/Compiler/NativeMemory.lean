module
public import Human.Compiler.NativeArithmetic
public import Human.Circuits.InitsTeardowns.Native.Model
public import Human.Helpers.Context.PaddingBoundary.Model

@[expose] public section
namespace Airbender.Compiler.NativeMemory
open NativeArithmetic

/-- Public challenges of the native extension-field caches and products. -/
structure Challenges (E : Type) [CommRing E] where
  /-- The embedding, additive challenge and six weights of the shared memory argument. -/
  memory : InitsTeardowns.Native.Parameters babyBearModulus E
  /-- The lookup linearization challenge. -/
  lookupAlpha : E

variable {E : Type} [CommRing E]

/-- A base-field value in the extension ring. -/
def Challenges.embed (challenges : Challenges E) (value : F) : E := challenges.memory.embed value

/-- One memory-bank column in the extension ring. -/
def Challenges.column (challenges : Challenges E) (physical : GKRAddress → F) (offset : Nat) : E :=
  challenges.embed (physical (.BaseLayerMemory offset))

/-- The address-space term: a constant, the RAM flag, or one minus the register flag.
    Source: `gkr_eval_ir/src/lower/memory.rs`, `address_space_term`. -/
def addressSpace (challenges : Challenges E) (physical : GKRAddress → F) :
    CompiledAddressSpaceRelationStrict → E
  | .Constant value => challenges.embed value.val
  | .IsRam offset => challenges.column physical offset
  | .IsRegister offset => 1 - challenges.column physical offset

/-- The weighted address limbs. The generic address form has no verifier semantics.
    Source: `gkr_eval_ir/src/lower/memory.rs`, `address_terms`. -/
def address (challenges : Challenges E) (physical : GKRAddress → F) :
    CompiledAddressStrict → Option E
  | .ConstantU16 value => some (challenges.memory.weights 0 * challenges.embed value.val)
  | .Constant value => some (challenges.memory.weights 0 * challenges.embed value.val)
  | .U16Space offset => some (challenges.memory.weights 0 * challenges.column physical offset)
  | .U32Space offsets => match offsets.values.toList with
    | [low, high] => some (challenges.memory.weights 0 * challenges.column physical low +
        challenges.memory.weights 1 * challenges.column physical high)
    | _ => none
  | .U32SpaceSpecialIndirect base dynamic offset high =>
    let dynamicTerm := match dynamic with
      | none => 0
      | some (scale, input) => challenges.embed scale.val * challenges.column physical input
    some (challenges.memory.weights 0 *
        (challenges.column physical base + challenges.embed offset.val + dynamicTerm) +
      challenges.memory.weights 1 * challenges.column physical high)
  | .U32SpaceGeneric _ => none

/-- The weighted timestamp limbs. The low limb carries the constant offset.
    Source: `gkr_eval_ir/src/lower/memory.rs`, `timestamp_terms`. -/
def timestamp (challenges : Challenges E) (physical : GKRAddress → F) (offset : U32) :
    CompiledMemoryTimestamp → Option E
  | .Zero => some 0
  | .Normal limbs => match limbs.values.toList with
    | [low, high] => some (challenges.memory.weights 2 *
        (challenges.column physical low + challenges.embed offset.val) +
      challenges.memory.weights 3 * challenges.column physical high)
    | _ => none

/-- The weighted value limbs. Byte limbs recompose each 16-bit half.
    Source: `gkr_eval_ir/src/lower/memory.rs`, `value_terms`. -/
def value (challenges : Challenges E) (physical : GKRAddress → F) :
    RamWordRepresentation → Option E
  | .Zero => some 0
  | .U16Limbs limbs => match limbs.values.toList with
    | [low, high] => some (challenges.memory.weights 4 * challenges.column physical low +
        challenges.memory.weights 5 * challenges.column physical high)
    | _ => none
  | .U8Limbs bytes => match bytes.values.toList with
    | [first, second, third, fourth] => some (challenges.memory.weights 4 *
        (challenges.column physical first + challenges.embed 256 * challenges.column physical second) +
      challenges.memory.weights 5 *
        (challenges.column physical third + challenges.embed 256 * challenges.column physical fourth))
    | _ => none

/-- The memory tuple: the additive challenge plus the address-space, address, timestamp and value terms.
    Source: `gkr_eval_ir/src/lower/memory.rs`, `lower_memory_tuple`. -/
def tuple (challenges : Challenges E) (physical : GKRAddress → F)
    (relation : SpecialMemoryContributionRelation) : Option E := do
  let addressTerm ← address challenges physical relation.address
  let timestampTerm ← timestamp challenges physical relation.timestamp_offset relation.timestamp
  let valueTerm ← value challenges physical relation.value
  return challenges.memory.additive + addressSpace challenges physical relation.address_space +
    addressTerm + timestampTerm + valueTerm

/-- The alpha-folded column values. Source: `gkr_eval_ir/src/lower/lookup.rs`, `folded_lookup`. -/
def fold (challenges : Challenges E) (columns : List F) : E :=
  (columns.zipIdx.map fun (column, index) => challenges.lookupAlpha ^ index * challenges.embed column).sum

/-- An extension cache carries its native value. Scalar caches are base-field caches of `NativeArithmetic`. -/
def CacheHolds (challenges : Challenges E) (physical : GKRAddress → F) (values : GKRAddress → E)
    (output : GKRAddress) : GKRCacheRelation → Prop
  | .SingleColumnLookup _ _ => True
  | .MemoryTuple relation => tuple challenges physical relation = some (values output)
  | .VectorizedLookup relation =>
    values output = fold challenges (relation.columns.toList.map fun column => linear column physical)
  | .VectorizedLookupSetup addresses => values output = fold challenges (addresses.toList.map physical)

/-- An extension gate computes its output: copies, vector materialization and the RAM products.
    The mask gate reads the base-field execute wire. Lookup aggregation gates have the
    `NativeLookups` interface. The initialization pair has the `InitsTeardowns.Native` interface. -/
def GateHolds (challenges : Challenges E) (physical : GKRAddress → F) (values : GKRAddress → E) :
    GKRRelation → Prop
  | .CopyInExtensionField input output => values output = values input
  | .MaterializedVectorLookupInput relation output =>
    values output = fold challenges (relation.columns.toList.map fun column => linear column physical)
  | .InitialGrandProductFromCaches input output => match input.values.toList with
    | [left, right] => values output = values left * values right
    | _ => False
  | .InitialGrandProductWithoutCaches input output => match input.values.toList with
    | [left, right] => ∃ leftValue rightValue, tuple challenges physical left = some leftValue ∧
        tuple challenges physical right = some rightValue ∧ values output = leftValue * rightValue
    | _ => False
  | .MaterializeGrandProductTermExpression input output => tuple challenges physical input = some (values output)
  | .TrivialProduct input output => match input.values.toList with
    | [left, right] => values output = values left * values right
    | _ => False
  | .MaskIntoIdentityProduct input mask output =>
    values output = PaddingBoundary.mask (challenges.embed (physical mask)) (values input)
  | _ => True

/-- All native extension caches and extension gates of the compiled layers hold.
    `physical` gives every base-field wire and `values` gives every extension wire. -/
def Holds (circuit : Circuit) (challenges : Challenges E) (physical : GKRAddress → F)
    (values : GKRAddress → E) : Prop :=
  ∀ layer ∈ circuit.layers,
    (∀ entry ∈ layer.cached_relations, CacheHolds challenges physical values entry.1 entry.2) ∧
    (∀ gate ∈ layer.gates ++ layer.gates_with_external_connections,
      GateHolds challenges physical values gate.enforced_relation)

/-- The native RAM argument outputs, in output-map order: the read product, then the write product. -/
def ramOutputs (circuit : Circuit) : List GKRAddress :=
  (circuit.global_output_map.entries.toList.filter fun entry =>
    match entry.1 with
    | .PermutationProduct => true
    | _ => false).flatMap fun entry => entry.2.toList

/-- The native PC-state tuple: address space two, the PC limbs as data and the raw timestamp. -/
def stateToken (state : PCState.State babyBearModulus) : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 2 (Nat.pair 0 0), state.timestamp, Nat.pair state.pc.1.val state.pc.2.val⟩

/-- A CPU row reads every port token and its starting PC-state token. -/
def cpuReads {Kind : Type} [Trace.CircuitLayout Kind] (row : Trace.Row babyBearModulus Kind) :
    List (Trace.MemoryToken babyBearModulus) :=
  row.reads ++ [stateToken row.start]

/-- A CPU row writes every port token and its final PC-state token. -/
def cpuWrites {Kind : Type} [Trace.CircuitLayout Kind] (row : Trace.Row babyBearModulus Kind) :
    List (Trace.MemoryToken babyBearModulus) :=
  row.writes ++ [stateToken row.finish]

/-- The RAM read and write outputs are the execute-masked products of the encoded tokens. -/
def RamProducts (circuit : Circuit) (challenges : Challenges E) (values : GKRAddress → E)
    (execute : F) (reads writes : List (Trace.MemoryToken babyBearModulus)) : Prop :=
  (ramOutputs circuit).map values =
    [PaddingBoundary.mask (challenges.embed execute) (reads.map challenges.memory.encode).prod,
     PaddingBoundary.mask (challenges.embed execute) (writes.map challenges.memory.encode).prod]

end Airbender.Compiler.NativeMemory
