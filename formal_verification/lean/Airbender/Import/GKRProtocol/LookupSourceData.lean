import Airbender.Proofs.GKRProtocol.BaseEncoding
import Airbender.Import.GKRCompiler.Import

namespace Airbender.Compiler.LookupSourceData
set_option warningAsError true

inductive Input where
  | address : GKRAddress → Input
  | scalar : SingleColumnLookupRelation → Input
  | vector : VectorLookupRelation → Input
  | setup : Array GKRAddress → Input

structure Operand where
  weight : LookupWeight
  input : Input

private def query (input : Input) : Operand := ⟨.one, input⟩
private def table (multiplicity : GKRAddress) (input : Input) : Operand := ⟨.negativeMultiplicity multiplicity, input⟩

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

def baseRecipe (row : LinearRelation) : NativeBaseRecipe :=
  row.linear_terms.foldl
    (fun result (coefficient, address) => .add result (.scale coefficient.raw.val (.input address)))
    (.constant row.constant.raw.val)

def encoding : Input → NativeLookupEncoding
  | .address address => .scalar (.input address)
  | .scalar row => .scalar (baseRecipe row.input)
  | .vector row => .vector (row.columns.toList.map baseRecipe)
  | .setup addresses => .vector (addresses.toList.map AffineProgram.input)

end Airbender.Compiler.LookupSourceData
