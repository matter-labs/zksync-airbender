module
public import Human.Compiler.NativeArithmetic
public import Human.Compiler.LookupArgument
public import Std.Data.TreeMap.Basic
public import Mathlib.Data.Nat.Pairing

@[expose] public section
namespace Airbender.Compiler.NativeLookups
open NativeArithmetic

/-- The native query weight or setup multiplicity. -/
inductive Weight where
  | one
  | column : GKRAddress → Weight
  | negativeMultiplicity : GKRAddress → Weight

/-- Read the uncompressed native weight. -/
def Weight.value (physical : GKRAddress → F) : Weight → F
  | .one => 1
  | .column address => physical address
  | .negativeMultiplicity address => -physical address

inductive Input where
  | address : GKRAddress → Input
  | scalar : SingleColumnLookupRelation → Input
  | vector : VectorLookupRelation → Input
  | setup : Array GKRAddress → Input

/-- One actual primitive operand before alpha compression. -/
structure Operand where
  /-- The native numerator weight. -/
  weight : Weight
  /-- The actual scalar or vector input. -/
  input : Input

def query (input : Input) : Operand := ⟨.one, input⟩
def table (multiplicity : GKRAddress) (input : Input) : Operand := ⟨.negativeMultiplicity multiplicity, input⟩

def operands : GKRRelation → Except String (Array Operand)
  | .LookupPairFromBaseInputs input _ _ => pure (input.values.map (fun row => query (.scalar row)))
  | .LookupPairFromVectorInputs input _ => pure (input.values.map (fun row => query (.vector row)))
  | .LookupPairFromMaterializedBaseInputs input _ | .LookupPairFromMaterializedVectorInputs input _ =>
      pure (input.values.map (fun address => query (.address address)))
  | .LookupFromBaseInputsWithSetup input setup _ _ =>
      match setup.values.toList with
      | [multiplicity, value] => pure #[query (.scalar input), table multiplicity (.address value)]
      | _ => throw "invalid scalar setup pair"
  | .LookupFromMaterializedBaseInputWithSetup input setup _ |
    .LookupFromMaterializedVectorInputWithSetup input setup _ =>
      match setup.values.toList with
      | [multiplicity, value] => pure #[query (.address input), table multiplicity (.address value)]
      | _ => throw "invalid materialized setup pair"
  | .LookupFromVectorInputWithSetup input setup _ =>
      pure #[query (.vector input), table setup.1 (.setup setup.2)]
  | .LookupWithCachedDensAndSetup input setup _ =>
      match input.values.toList, setup.values.toList with
      | [mask, value], [multiplicity, valueSetup] =>
          pure #[⟨.column mask, .address value⟩, table multiplicity (.address valueSetup)]
      | _, _ => throw "invalid masked materialized lookup pair"
  | .LookupWithDensAndSetupExpressions input setup _ =>
      pure #[⟨.column input.1, .vector input.2⟩, table setup.1 (.setup setup.2)]
  | .LookupUnbalancedPairWithMaterializedBaseInputs _ remainder _ |
    .LookupUnbalancedPairWithMaterializedVectorInputs _ remainder _ => pure #[query (.address remainder)]
  | .LookupUnbalancedPairWithVectorInputs _ remainder _ => pure #[query (.vector remainder)]
  | .LookupPairFromCachedVectorInputs _ _ => throw "retired cached-vector lookup consumer"
  | .EnforceConstraintsMaxQuadratic _ => throw "retired batched arithmetic consumer"
  | .UnbalancedGrandProductWithCache _ _ _ => throw "retired unbalanced product consumer"
  | .LinearBaseFieldRelation _ _ | .MaxQuadratic _ _ _ | .EnforceSingleMaxQuadraticConstraint _ _ |
    .CopyInBaseField _ _ | .CopyInExtensionField _ _ | .InitialGrandProductFromCaches _ _ |
    .InitialGrandProductWithoutCaches _ _ | .MaterializeGrandProductTermExpression _ _ |
    .TrivialProduct _ _ | .MaskIntoIdentityProduct _ _ _ | .MaterializeSingleLookupInput _ _ _ |
    .MaterializedVectorLookupInput _ _ | .AggregateLookupRationalPair _ _ |
    .InitsOrTeardownsInitialPair _ _ _ _ => pure #[]

inductive Definition where
  | cache : GKRAddress → GKRCacheRelation → Definition
  | copy : GKRAddress → GKRAddress → Definition
  | scalar : GKRAddress → SingleColumnLookupRelation → Definition
  | vector : GKRAddress → VectorLookupRelation → Definition

def Definition.output : Definition → GKRAddress
  | .cache output _ | .copy output _ | .scalar output _ | .vector output _ => output

def Definition.input : Definition → Except String Input
  | .copy _ input => pure (.address input)
  | .scalar _ row => pure (.scalar row)
  | .vector _ row => pure (.vector row)
  | .cache _ (.SingleColumnLookup row _) => pure (.scalar row)
  | .cache _ (.VectorizedLookup row) => pure (.vector row)
  | .cache _ (.VectorizedLookupSetup addresses) => pure (.setup addresses)
  | .cache _ (.MemoryTuple _) => throw "a memory tuple is not a source lookup encoding"

def definitions (circuit : Circuit) : Array Definition :=
  (circuit.layers.toList.flatMap (fun (layer : GKRLayerDescription) =>
    layer.cached_relations.toList.map (fun entry => Definition.cache entry.1 entry.2)) ++
   circuit.layers.toList.flatMap (fun (layer : GKRLayerDescription) =>
    (layer.gates ++ layer.gates_with_external_connections).toList.filterMap fun gate =>
      match gate.enforced_relation with
      | .CopyInBaseField input output | .CopyInExtensionField input output => some (Definition.copy output input)
      | .MaterializeSingleLookupInput row output _ => some (Definition.scalar output row)
      | .MaterializedVectorLookupInput row output => some (Definition.vector output row)
      | _ => none)).toArray

def head (definitions : Array Definition) : List Nat → Input → Except String Input
  | [], input => pure input
  | index :: rest, .address address => do
      let some definition := definitions[index]? | throw "operand definition index outside actual native list"
      unless definition.output == address do throw "selected definition does not define the actual operand head"
      head definitions rest (← definition.input)
  | _ :: _, _ => throw "operand expansion continues past its actual base-column encoding"


/-- A selector names one actual primitive operand and its cache or copy expansion path. -/
structure Selector where
  /-- The public setup group: generic, 16-bit range or timestamp range. -/
  group : Fin 3
  /-- The gate position in layer order. -/
  gate : Nat
  /-- The operand position of that primitive gate. -/
  operand : Nat
  /-- Actual cache, copy or materialization definitions that expand the operand. -/
  expansion : List Nat

/-- The actual compiled gates in layer and native gate order. -/
def compiledGates (circuit : Circuit) : Array GateArtifacts :=
  circuit.layers.flatMap fun layer => layer.gates ++ layer.gates_with_external_connections

/-- All non-setup primitive operand positions in the actual compiled layers. -/
def queryLocators (circuit : Circuit) : Except String (List (Nat × Nat)) := do
  let groups ← (compiledGates circuit).toList.zipIdx.mapM fun (gate, gateIndex) => do
    let inputs ← operands gate.enforced_relation
    return inputs.toList.zipIdx.filterMap fun (operand, operandIndex) =>
      match operand.weight with
      | .negativeMultiplicity _ => none
      | _ => some (gateIndex, operandIndex)
  return groups.flatten

/-- Resolve a selector against retained gate and definition arrays. -/
def selectFrom (gates : Array GateArtifacts) (definitions : Array Definition)
    (selector : Selector) : Except String Operand := do
  let some gate := gates[selector.gate]? | throw "Native lookup gate is absent"
  let operands ← operands gate.enforced_relation
  let some operand := operands[selector.operand]? | throw "Native lookup operand is absent"
  return ⟨operand.weight, ← head definitions selector.expansion operand.input⟩

/-- Resolve a selector against its actual compiled gate and definition chain. -/
def select (circuit : Circuit) (selector : Selector) : Except String Operand :=
  selectFrom (compiledGates circuit) (definitions circuit) selector

/-- Retain each native array once when checking a selector batch. -/
def resolvedAll (circuit : Circuit) (selectors : List Selector) : Bool :=
  let gates := compiledGates circuit
  let definitions := definitions circuit
  selectors.all fun selector =>
    match selectFrom gates definitions selector with | .ok _ => true | .error _ => false

/-- Address tags occupy distinct residues modulo eight. Pairing retains both coordinates of layered addresses. -/
def chainAddress : GKRAddress → Nat
  | .BaseLayerWitness index => 8 * index
  | .BaseLayerMemory index => 8 * index + 1
  | .InnerLayer layer offset => 8 * Nat.pair layer offset + 2
  | .Setup index => 8 * index + 3
  | .VirtualSetup kind => 8 * (match kind with
      | .RangeCheck16Bits => 0 | .RangeCheckTimestamp => 1
      | .InitsAndTeardownsLow => 2 | .InitsAndTeardownsHigh => 3) + 4
  | .ScratchSpace index => 8 * index + 5
  | .Cached layer offset => 8 * Nat.pair layer offset + 6

/-- A rational chain records the same query positions for its numerator and denominator. -/
abbrev ChainStore := Std.TreeMap Nat (Bool × List (Nat × Nat))

/-- Read both parts of one actual rational chain. -/
def readChain (store : ChainStore) (pair : List GKRAddress) : Except String (List (Nat × Nat)) := do
  let [numerator, denominator] := pair | throw "Native lookup output is not a pair"
  let some left := store.get? (chainAddress numerator)
    | throw "Native lookup numerator has no chain"
  let some right := store.get? (chainAddress denominator)
    | throw "Native lookup denominator has no chain"
  unless !left.1 && right.1 && left.2 == right.2 do
    throw "Native lookup pair has different chains"
  return left.2

/-- Write the two distinct parts of one native rational chain. -/
def writeChain (store : ChainStore) (pair : List GKRAddress) (queries : List (Nat × Nat)) :
    Except String ChainStore := do
  let [numerator, denominator] := pair | throw "Native lookup output is not a pair"
  unless numerator != denominator do throw "Native lookup pair aliases its two parts"
  return (store.insert (chainAddress numerator) (false, queries)).insert (chainAddress denominator) (true, queries)

/-- Follow native copies, primitive lookup leaves and rational additions in gate order. -/
def chainStep (store : ChainStore) (indexed : GateArtifacts × Nat) : Except String ChainStore := do
  let (gate, index) := indexed
  match gate.enforced_relation with
  | .CopyInExtensionField input output =>
      match store.get? (chainAddress input) with
      | some chain => return store.insert (chainAddress output) chain
      | none => return store
  | .AggregateLookupRationalPair input output =>
      let [leftInput, rightInput] := input.values.toList
        | throw "Native lookup addition does not have two inputs"
      let left ← readChain store leftInput.values.toList
      let right ← readChain store rightInput.values.toList
      writeChain store output.values.toList (left ++ right)
  | .LookupPairFromBaseInputs _ output _ | .LookupPairFromVectorInputs _ output |
    .LookupPairFromMaterializedBaseInputs _ output | .LookupPairFromMaterializedVectorInputs _ output =>
      writeChain store output.values.toList [(index, 0), (index, 1)]
  | .LookupFromBaseInputsWithSetup _ _ output _ | .LookupFromVectorInputWithSetup _ _ output |
    .LookupFromMaterializedBaseInputWithSetup _ _ output |
    .LookupFromMaterializedVectorInputWithSetup _ _ output |
    .LookupWithCachedDensAndSetup _ _ output | .LookupWithDensAndSetupExpressions _ _ output =>
      writeChain store output.values.toList [(index, 0)]
  | .LookupUnbalancedPairWithMaterializedBaseInputs input _ output |
    .LookupUnbalancedPairWithMaterializedVectorInputs input _ output |
    .LookupUnbalancedPairWithVectorInputs input _ output =>
      let previous ← readChain store input.values.toList
      writeChain store output.values.toList (previous ++ [(index, 0)])
  | _ => return store

/-- Each public lookup output identifies the group of every query in its native chain. -/
def chainGroups (circuit : Circuit) : Except String (List ((Nat × Nat) × Fin 3)) := do
  let store ← (compiledGates circuit).toList.zipIdx.foldlM chainStep ∅
  let groups ← circuit.global_output_map.entries.toList.mapM fun (kind, output) => do
    let group : Option (Fin 3) := match kind with
      | .GenericLookup => some 0
      | .Lookup16Bits => some 1
      | .LookupTimestamps => some 2
      | _ => none
    match group with
    | none => return []
    | some group => return (← readChain store output.toList).map (fun query => (query, group))
  return groups.flatten

/-- Each query selector belongs to exactly one native output chain with the same group. -/
def groupsAgree (circuit : Circuit) (selectors : List Selector) : Bool :=
  match chainGroups circuit with
  | .error _ => false
  | .ok groups => selectors.all fun selector =>
      (groups.filter (fun entry => entry.1 == (selector.gate, selector.operand))).map Prod.snd == [selector.group]

/-- Evaluate actual sparse columns before alpha compression. -/
def Input.fields (physical : GKRAddress → F) : Input → List F
  | .address wire => [physical wire]
  | .scalar row => [linear row.input physical]
  | .vector row => row.columns.toList.map (fun column => linear column physical)
  | .setup addresses => addresses.toList.map physical

/-- Every enabled native tuple of one setup group. A failed expansion rejects the certificate. -/
def requests (circuit : Circuit) (selectors : List Selector) (physical : GKRAddress → F)
    (group : Fin 3) : Except String (List (List F)) := do
  let operands ← (selectors.filter (fun selector => selector.group == group)).mapM (select circuit)
  return (operands.filter (fun operand => operand.weight.value physical != 0)).map
    (fun operand => operand.input.fields physical)

/-- Exact tuple matching for every enabled native primitive query. The table rows are public setup inputs. -/
structure Arguments {Index : Type} (circuit : Circuit) (selectors : List Selector)
    (physical : GKRAddress → F) (tables : Fin 3 → Index → List F) where
  /-- The complete uncompressed emitted tuples of each native lookup group. -/
  tuples : Fin 3 → List (List F)
  /-- The tuples are the actual primitive operands at the retained native selectors. -/
  binding : ∀ group, requests circuit selectors physical group = .ok (tuples group)
  /-- Natural multiplicities give exact matching with independently interpreted setup rows. -/
  matching : GroupedLookupArguments tables tuples

end Airbender.Compiler.NativeLookups
