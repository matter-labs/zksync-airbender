import Airbender.Import.Parse
import Airbender.Review.Circuits.Initialization.Model

namespace Airbender.Initialization.Import
open Lean
set_option warningAsError true

inductive Flavor where
  | standalone | unified
  deriving Repr, DecidableEq

/-- Enumerate every native producer, including unsupported relation kinds.
    An unsupported producer on a required dependency is rejected explicitly. -/
def outputs : GKRRelation → List GKRAddress
  | .LinearBaseFieldRelation _ output => [output]
  | .MaxQuadratic _ _ output => [output]
  | .EnforceSingleMaxQuadraticConstraint _ _ => []
  | .EnforceConstraintsMaxQuadratic _ => []
  | .CopyInBaseField _ output => [output]
  | .CopyInExtensionField _ output => [output]
  | .InitialGrandProductFromCaches _ output => [output]
  | .InitialGrandProductWithoutCaches _ output => [output]
  | .UnbalancedGrandProductWithCache _ _ output => [output]
  | .MaterializeGrandProductTermExpression _ output => [output]
  | .TrivialProduct _ output => [output]
  | .MaskIntoIdentityProduct _ _ output => [output]
  | .MaterializeSingleLookupInput _ output _ => [output]
  | .MaterializedVectorLookupInput _ output => [output]
  | .LookupWithCachedDensAndSetup _ _ output => output.values.toList
  | .LookupWithDensAndSetupExpressions _ _ output => output.values.toList
  | .LookupPairFromBaseInputs _ output _ => output.values.toList
  | .LookupPairFromMaterializedBaseInputs _ output => output.values.toList
  | .LookupFromBaseInputsWithSetup _ _ output _ => output.values.toList
  | .LookupFromMaterializedBaseInputWithSetup _ _ output => output.values.toList
  | .LookupUnbalancedPairWithMaterializedBaseInputs _ _ output => output.values.toList
  | .LookupPairFromVectorInputs _ output => output.values.toList
  | .LookupPairFromMaterializedVectorInputs _ output => output.values.toList
  | .LookupFromVectorInputWithSetup _ _ output => output.values.toList
  | .LookupFromMaterializedVectorInputWithSetup _ _ output => output.values.toList
  | .LookupPairFromCachedVectorInputs _ output => output.values.toList
  | .LookupUnbalancedPairWithVectorInputs _ _ output => output.values.toList
  | .LookupUnbalancedPairWithMaterializedVectorInputs _ _ output => output.values.toList
  | .AggregateLookupRationalPair _ output => output.values.toList
  | .InitsOrTeardownsInitialPair _ _ output _ => [output]

private def two (values : Array α) : Except String (α × α) :=
  match values.toList with
  | [left, right] => .ok (left, right)
  | _ => .error "RAM boundary requires an exact two-element native array"

private def port : GKRAddress → Except String Port
  | .InnerLayer layer offset => .ok ⟨layer, offset⟩
  | _ => .error "unsupported RAM-boundary input: expected an uncached inner-layer wire"

private def memoryColumn (width : Nat) : GKRAddress → Except String Nat
  | .BaseLayerMemory index =>
      if index < width then .ok index else .error "RAM teardown column is outside memory layout"
  | _ => .error "RAM teardown must read the actual base-layer memory bank"

private def layoutColumns (circuit : Circuit) : Except String (Array Columns) :=
  circuit.memory_layout.teardown_sets.mapM fun (time, value) => do
    let (timeLo, timeHi) ← two time.values
    let (valueLo, valueHi) ← two value.values
    return ⟨← memoryColumn circuit.memory_layout.total_width timeLo,
      ← memoryColumn circuit.memory_layout.total_width timeHi,
      ← memoryColumn circuit.memory_layout.total_width valueLo,
      ← memoryColumn circuit.memory_layout.total_width valueHi⟩

private def scalarColumns (time value : Fixed 2 Nat) : Except String Columns := do
  let (timeLo, timeHi) ← two time.values
  let (valueLo, valueHi) ← two value.values
  return ⟨timeLo, timeHi, valueLo, valueHi⟩

private def decodeGate (columns : Array Columns) : GKRRelation → Except String Gate
  | .TrivialProduct input output => do
      let (left, right) ← two input.values
      return .product (← port output) (← port left) (← port right)
  | .CopyInExtensionField input output => do
      return .copy (← port output) (← port input)
  | .InitsOrTeardownsInitialPair mode setup output sets => do
      match setup.values.toList with
      | [.VirtualSetup .InitsAndTeardownsLow, .VirtualSetup .InitsAndTeardownsHigh] => pure ()
      | _ => throw "RAM pair has incorrect native virtual address inputs"
      let (leftSet, rightSet) ← two sets.values
      let some leftLayout := columns[leftSet]? | throw "RAM pair left set is outside layout"
      let some rightLayout := columns[rightSet]? | throw "RAM pair right set is outside layout"
      let (phase, left, right) ← match mode with
        | .Init => pure (Phase.initial, leftLayout, rightLayout)
        | .Teardown leftTime leftValue rightTime rightValue => do
            let left ← scalarColumns leftTime leftValue
            let right ← scalarColumns rightTime rightValue
            unless left == leftLayout && right == rightLayout do
              throw "RAM pair columns disagree with the independently parsed teardown layout"
            pure (Phase.terminal, left, right)
      return .pair (← port output) ⟨phase, leftSet, left⟩ ⟨phase, rightSet, right⟩
  | _ => .error "unsupported relation on a required RAM-boundary dependency"

private def allGates (circuit : Circuit) : Array GateArtifacts :=
  circuit.layers.flatMap fun layer => layer.gates ++ layer.gates_with_external_connections

private def producer (circuit : Circuit) (target : GKRAddress) : Except String GKRRelation := do
  if circuit.layers.any (fun layer => layer.cached_relations.any fun entry => entry.1 == target) then
    throw "cached RAM-boundary producer is unsupported"
  let found := (allGates circuit).filter fun gate => (outputs gate.enforced_relation).contains target
  match found.toList with
  | [gate] => pure gate.enforced_relation
  | [] => throw "missing RAM-boundary producer"
  | _ => throw "ambiguous or duplicated RAM-boundary producer"

private def address (wire : Port) : GKRAddress := .InnerLayer wire.layer wire.offset

private partial def buildTree (circuit : Circuit) (columns : Array Columns)
    (target : GKRAddress) (visiting : List GKRAddress) : Except String (Tree × List Gate) := do
  if visiting.contains target then throw "cyclic RAM-boundary producer graph"
  let gate ← decodeGate columns (← producer circuit target)
  let visiting := target :: visiting
  match gate with
  | .pair output left right => return (.pair output left right, [gate])
  | .product output left right =>
      let (lhs, lhsGates) ← buildTree circuit columns (address left) visiting
      let (rhs, rhsGates) ← buildTree circuit columns (address right) visiting
      return (.product output lhs rhs, lhsGates ++ rhsGates ++ [gate])
  | .copy output input =>
      let (source, gates) ← buildTree circuit columns (address input) visiting
      return (.copy output source, gates ++ [gate])

private def selectedOutput (flavor : Flavor) : OutputType → Bool
  | .PermutationProduct => flavor == .standalone
  | .InitsAndTeardownsProduct => flavor == .unified
  | _ => false

/-- Extract the complete standalone graph or the exact inline RAM dependency
    slice. No expected tree, output value or schedule is a caller premise. -/
def extract (flavor : Flavor) (circuit : Circuit) (sourceBytes : String := "") :
    Except String Artifact := do
  let some wordBits := circuit.memory_layout.inits_and_teardowns_word_bits
    | throw "native layout lacks initialization word bits"
  unless wordBits.val == 2 do throw "only the actual four-byte native RAM geometry is supported"
  let log := circuit.trace_len.log2
  unless 2 ^ log == circuit.trace_len && 14 ≤ log && log + wordBits.val ≤ 32 do
    throw "invalid native RAM trace geometry"
  let columns ← layoutColumns circuit
  unless 0 < columns.size do throw "native RAM teardown layout is empty"
  let roots := circuit.global_output_map.entries.filter fun entry => selectedOutput flavor entry.1
  let output ← match roots.toList with
    | [(_, outputs)] => pure outputs
    | _ => throw "missing or ambiguous native RAM global output mapping"
  let (terminalRoot, initialRoot) ← two output
  let (terminal, terminalGates) ← buildTree circuit columns terminalRoot []
  let (initial, initialGates) ← buildTree circuit columns initialRoot []
  unless terminal.leaves.all (fun leaf => leaf.phase == .terminal) &&
      initial.leaves.all (fun leaf => leaf.phase == .initial) do
    throw "native RAM output mapping swaps or mixes initialization and teardown"
  let gates := (terminalGates ++ initialGates).eraseDups.toArray
  if flavor == .standalone then
    unless gates.size == (allGates circuit).size do
      throw "standalone RAM graph has unsupported or disconnected relations"
  let highOffset := log + wordBits.val - 16
  return {
    layout := ⟨circuit.trace_len, wordBits.val, highOffset, 2 ^ highOffset,
      2 ^ (32 - log - wordBits.val), circuit.memory_layout.total_width, columns⟩
    gates, terminal, initial, sourceBytes }

def parse (flavor : Flavor) (source : String) : Except String Artifact := do
  extract flavor (← parseCircuit source) source

end Airbender.Initialization.Import
