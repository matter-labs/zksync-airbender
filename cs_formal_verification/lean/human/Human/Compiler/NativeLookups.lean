module
public import Human.Compiler.NativeArithmetic
public import Human.Compiler.LookupArgument

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

def definitions (circuit : Circuit) : Array Definition := Id.run do
  let mut result := #[]
  for layer in circuit.layers do
    for (output, relation) in layer.cached_relations do result := result.push (.cache output relation)
  for layer in circuit.layers do
    for gate in layer.gates ++ layer.gates_with_external_connections do
      match gate.enforced_relation with
      | .CopyInBaseField input output | .CopyInExtensionField input output => result := result.push (.copy output input)
      | .MaterializeSingleLookupInput row output _ => result := result.push (.scalar output row)
      | .MaterializedVectorLookupInput row output => result := result.push (.vector output row)
      | _ => pure ()
  return result

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

/-- Resolve a selector against its actual compiled gate and definition chain. -/
def select (circuit : Circuit) (selector : Selector) : Except String Operand := do
  let some gate := (compiledGates circuit)[selector.gate]? | throw "Native lookup gate is absent"
  let operands ← operands gate.enforced_relation
  let some operand := operands[selector.operand]? | throw "Native lookup operand is absent"
  return ⟨operand.weight, ← head (definitions circuit) selector.expansion operand.input⟩

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
