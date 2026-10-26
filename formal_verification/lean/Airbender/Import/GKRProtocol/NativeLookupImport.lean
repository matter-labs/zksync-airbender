import Airbender.Proofs.GKRProtocol.NativeLookup
import Airbender.Import.GKRProtocol.CacheImport

namespace Airbender.Compiler.NativeLookupImport
open Lean Elab Command
set_option warningAsError true

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .InnerLayer layer index => `(GKRAddress.InnerLayer $(quote layer) $(quote index))
  | .Cached layer index => `(GKRAddress.Cached $(quote layer) $(quote index))
  | .Setup index => `(GKRAddress.Setup $(quote index))
  | .ScratchSpace _ => throwError "a native lookup consumer cannot read ScratchSpace"
  | .VirtualSetup kind => do
      let kind ← match kind with
        | .RangeCheck16Bits => `(VirtualSetupPoly.RangeCheck16Bits)
        | .RangeCheckTimestamp => `(VirtualSetupPoly.RangeCheckTimestamp)
        | .InitsAndTeardownsLow => `(VirtualSetupPoly.InitsAndTeardownsLow)
        | .InitsAndTeardownsHigh => `(VirtualSetupPoly.InitsAndTeardownsHigh)
      `(GKRAddress.VirtualSetup $kind)

private def portsData (addresses : Array GKRAddress) : CommandElabM RationalPorts := do
  let [numerator, denominator] := addresses.toList | throwError "native rational pair has wrong width"
  return ⟨numerator, denominator⟩

private def pairSyntax (addresses : Array GKRAddress) : CommandElabM (TSyntax `term) := do
  let ports ← portsData addresses
  `(RationalPorts.mk $(← addressSyntax ports.numerator) $(← addressSyntax ports.denominator))

private def operand (address : GKRAddress) : CommandElabM (TSyntax `term) := do
  `(AffineProgram.input (R := CacheCoefficient) $(← addressSyntax address))

private def scalar (row : SingleColumnLookupRelation) : CommandElabM (TSyntax `term) :=
  CacheImport.program (.SingleColumnLookup row 0)

private def vector (row : VectorLookupRelation) : CommandElabM (TSyntax `term) :=
  CacheImport.program (.VectorizedLookup row)

structure Pieces where
  native : TSyntax `term
  step : TSyntax `term
  leaves : Array (TSyntax `term)
  equalities : Nat
  stepData : LookupStep

private def pair (output : Fixed 2 GKRAddress) (left right : TSyntax `term) (index : Nat) : CommandElabM Pieces := do
  let data ← portsData output.values
  let output ← pairSyntax output.values
  return ⟨← `(NativeLookupGate.pair $output $left $right),
    ← `(LookupStep.seed $output $(quote index) $(quote (index + 1))),
    #[← `(NativeLookupLeaf.mk LookupWeight.one $left), ← `(NativeLookupLeaf.mk LookupWeight.one $right)], 3, .seed data index (index + 1)⟩

private def setup (output : Fixed 2 GKRAddress) (mask input multiplicity table : TSyntax `term)
    (index : Nat) : CommandElabM Pieces := do
  let data ← portsData output.values
  let output ← pairSyntax output.values
  return ⟨← `(NativeLookupGate.setup $output $mask $input $multiplicity $table),
    ← `(LookupStep.seed $output $(quote index) $(quote (index + 1))),
    #[← `(NativeLookupLeaf.mk $mask $input),
      ← `(NativeLookupLeaf.mk (LookupWeight.negativeMultiplicity $multiplicity) $table)], 3, .seed data index (index + 1)⟩

private def extend (output input : Fixed 2 GKRAddress) (remainder : TSyntax `term)
    (index : Nat) : CommandElabM Pieces := do
  let outData ← portsData output.values
  let inData ← portsData input.values
  let output ← pairSyntax output.values
  let input ← pairSyntax input.values
  return ⟨← `(NativeLookupGate.extend $output $input $remainder),
    ← `(LookupStep.extend $output $input $(quote index)), #[← `(NativeLookupLeaf.mk LookupWeight.one $remainder)], 3,
    .extend outData inData index⟩

/-- Every relevant native opcode is explicit. Other opcodes belong to the
arithmetic/product subsystems; retired lookup variants fail closed. -/
private def pieces (index : Nat) : GKRRelation → CommandElabM (Option Pieces)
  | .LookupPairFromBaseInputs input output _ => do
      let [left, right] := input.values.toList | throwError "invalid scalar lookup pair"
      return some (← pair output (← scalar left) (← scalar right) index)
  | .LookupPairFromVectorInputs input output => do
      let [left, right] := input.values.toList | throwError "invalid vector lookup pair"
      return some (← pair output (← vector left) (← vector right) index)
  | .LookupPairFromMaterializedBaseInputs input output
    | .LookupPairFromMaterializedVectorInputs input output => do
      let [left, right] := input.values.toList | throwError "invalid materialized lookup pair"
      return some (← pair output (← operand left) (← operand right) index)
  | .LookupFromBaseInputsWithSetup input source output _ => do
      let [multiplicity, table] := source.values.toList | throwError "invalid scalar setup pair"
      return some (← setup output (← `(LookupWeight.one)) (← scalar input)
        (← addressSyntax multiplicity) (← operand table) index)
  | .LookupFromMaterializedBaseInputWithSetup input source output
    | .LookupFromMaterializedVectorInputWithSetup input source output => do
      let [multiplicity, table] := source.values.toList | throwError "invalid materialized setup pair"
      return some (← setup output (← `(LookupWeight.one)) (← operand input)
        (← addressSyntax multiplicity) (← operand table) index)
  | .LookupFromVectorInputWithSetup input source output => do
      return some (← setup output (← `(LookupWeight.one)) (← vector input)
        (← addressSyntax source.1) (← CacheImport.program (.VectorizedLookupSetup source.2)) index)
  | .LookupWithCachedDensAndSetup input source output => do
      let [mask, payload] := input.values.toList | throwError "invalid masked lookup input"
      let [multiplicity, table] := source.values.toList | throwError "invalid masked lookup setup"
      return some (← setup output (← `(LookupWeight.column $(← addressSyntax mask))) (← operand payload)
        (← addressSyntax multiplicity) (← operand table) index)
  | .LookupWithDensAndSetupExpressions input source output => do
      return some (← setup output (← `(LookupWeight.column $(← addressSyntax input.1))) (← vector input.2)
        (← addressSyntax source.1) (← CacheImport.program (.VectorizedLookupSetup source.2)) index)
  | .LookupUnbalancedPairWithMaterializedBaseInputs input remainder output
    | .LookupUnbalancedPairWithMaterializedVectorInputs input remainder output => do
      return some (← extend output input (← operand remainder) index)
  | .LookupUnbalancedPairWithVectorInputs input remainder output => do
      return some (← extend output input (← vector remainder) index)
  | .AggregateLookupRationalPair input output => do
      let [left, right] := input.values.toList | throwError "invalid aggregate lookup inputs"
      let outData ← portsData output.values
      let leftData ← portsData left.values
      let rightData ← portsData right.values
      let output ← pairSyntax output.values
      let left ← pairSyntax left.values
      let right ← pairSyntax right.values
      return some ⟨← `(NativeLookupGate.add $output $left $right),
        ← `(LookupStep.add $output $left $right), #[], 3, .add outData leftData rightData⟩
  | .CopyInExtensionField input output => do
      let data := LookupStep.copy output input
      let input ← addressSyntax input
      let output ← addressSyntax output
      return some ⟨← `(NativeLookupGate.copy $output $input), ← `(LookupStep.copy $output $input), #[], 2, data⟩
  | .LookupPairFromCachedVectorInputs _ _ => throwError "retired cached-vector lookup consumer"
  | .EnforceConstraintsMaxQuadratic _ => throwError "retired batched arithmetic consumer"
  | .UnbalancedGrandProductWithCache _ _ _ => throwError "retired unbalanced product consumer"
  | .LinearBaseFieldRelation _ _ | .MaxQuadratic _ _ _ | .EnforceSingleMaxQuadraticConstraint _ _ |
    .CopyInBaseField _ _ | .InitialGrandProductFromCaches _ _ | .InitialGrandProductWithoutCaches _ _ |
    .MaterializeGrandProductTermExpression _ _ | .TrivialProduct _ _ | .MaskIntoIdentityProduct _ _ _ |
    .MaterializeSingleLookupInput _ _ _ | .MaterializedVectorLookupInput _ _ |
    .InitsOrTeardownsInitialPair _ _ _ _ => pure none

private def proofTuple (arity : Nat) : CommandElabM (TSyntax `term) := do
  if arity == 2 then `(⟨rfl, rfl⟩) else `(⟨rfl, rfl, rfl⟩)

private def checksSyntax (proofs : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(PredicateChecks.nil)
  for proof in proofs.reverse do result ← `(PredicateChecks.cons $proof $result)
  return result

private def treeSyntax : LookupTree Nat → CommandElabM (TSyntax `term)
  | .leaf index => `(LookupTree.leaf $(quote index))
  | .add left right => do `(LookupTree.add $(← treeSyntax left) $(← treeSyntax right))

private def environmentSyntax (environment : LookupEnvironment) : CommandElabM (TSyntax `term) := do
  let entries ← environment.toArray.mapM fun (address, meaning) => do
    let flag ← if meaning.denominator then `(true) else `(false)
    `(($(← addressSyntax address), LookupMeaning.mk $(← treeSyntax meaning.tree) $flag))
  `([$entries,*])

syntax (name := importNativeLookups) "import_native_lookups " ident " from " str : command

elab_rules : command
  | `(import_native_lookups $name:ident from $path:str) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair
      | .error error => throwError "invalid compiler pair for native lookup reduction: {error}"
    unless pair.format_version == 1 do throwError "unsupported compiler pair format"
    let mut gates : Array (TSyntax `term) := #[]
    let mut leaves : Array (TSyntax `term) := #[]
    let mut bindings : Array (TSyntax `term) := #[]
    let mut bindingNames : Array (TSyntax `ident) := #[]
    let mut equalityCounts : Array Nat := #[]
    let mut stepValues : Array LookupStep := #[]
    for layer in pair.circuit.layers do
      for gate in layer.gates ++ layer.gates_with_external_connections do
        if let some description ← pieces leaves.size gate.enforced_relation then
          let gateName := mkIdent (name.getId ++ Name.mkSimple s!"gate{gates.size}")
          elabCommand (← `(noncomputable def $gateName : NativeLookupGate := $(description.native)))
          let binding := mkIdent (name.getId ++ Name.mkSimple s!"binding{bindings.size}")
          elabCommand (← `(noncomputable def $binding : NativeLookupBinding :=
            ⟨$(quote gates.size), $(description.step)⟩))
          gates := gates.push (← `($gateName))
          bindings := bindings.push (← `($binding))
          bindingNames := bindingNames.push binding
          equalityCounts := equalityCounts.push description.equalities
          stepValues := stepValues.push description.stepData
          for leaf in description.leaves do
            let leafName := mkIdent (name.getId ++ Name.mkSimple s!"leaf{leaves.size}")
            elabCommand (← `(noncomputable def $leafName : NativeLookupLeaf := $leaf))
            leaves := leaves.push (← `($leafName))
    let native := mkIdent (name.getId ++ `gates)
    let registry := mkIdent (name.getId ++ `registry)
    let schedule := mkIdent (name.getId ++ `bindings)
    elabCommand (← `(noncomputable def $native : List NativeLookupGate := [$gates,*]))
    elabCommand (← `(noncomputable def $registry : List NativeLookupLeaf := [$leaves,*]))
    elabCommand (← `(noncomputable def $schedule : List NativeLookupBinding := [$bindings,*]))
    let mut proofs := #[]
    for index in [:bindings.size] do
      let binding := bindingNames[index]!
      let proof := mkIdent (name.getId ++ Name.mkSimple s!"bindingChecked{index}")
      elabCommand (← `(theorem $proof : ($binding).Valid $registry $native := $(← proofTuple equalityCounts[index]!)))
      proofs := proofs.push proof
    let valid := mkIdent (name.getId ++ `valid)
    elabCommand (← `(theorem $valid : ∀ binding ∈ $schedule, binding.Valid $registry $native :=
      PredicateChecks.all $(← checksSyntax proofs)))
    let initial := mkIdent (name.getId ++ `environment0)
    let initialSound := mkIdent (name.getId ++ `environmentSound0)
    elabCommand (← `(noncomputable def $initial : LookupEnvironment := []))
    elabCommand (← `(theorem $initialSound {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (values : GKRAddress → R) (_holds : ∀ gate ∈ $native, gate.Holds hom challenges gamma values) :
      ($initial).Sound values (NativeLookupLeaf.registryValue $registry hom challenges gamma values) := by
      intro address meaning member
      cases member))
    let mut previous := initial
    let mut previousSound := initialSound
    let mut environment : LookupEnvironment := []
    for block in [:(bindings.size + 31) / 32] do
      let first := block * 32
      let last := min (first + 32) bindings.size
      let selected := bindings.extract first last
      let selectedProofs := proofs.extract first last
      let segment := mkIdent (name.getId ++ Name.mkSimple s!"chunk{first}")
      let segmentValid := mkIdent (name.getId ++ Name.mkSimple s!"chunkValid{first}")
      elabCommand (← `(noncomputable def $segment : List NativeLookupBinding := [$selected,*]))
      elabCommand (← `(theorem $segmentValid : ∀ binding ∈ $segment, binding.Valid $registry $native :=
        PredicateChecks.all $(← checksSyntax selectedProofs)))
      let steps := (stepValues.extract first last).toList
      let some next := LookupStep.run steps environment
        | throwError "actual native lookup port trace fails in chunk {first}..{last}"
      environment := next
      let checkpoint := mkIdent (name.getId ++ Name.mkSimple s!"environment{last}")
      let checkpointSound := mkIdent (name.getId ++ Name.mkSimple s!"environmentSound{last}")
      let chunkChecked := mkIdent (name.getId ++ Name.mkSimple s!"chunkChecked{first}")
      let chunkReplayed := mkIdent (name.getId ++ Name.mkSimple s!"chunkReplayed{first}")
      elabCommand (← `(noncomputable def $checkpoint : LookupEnvironment := $(← environmentSyntax environment)))
      elabCommand (← `(theorem $chunkChecked : LookupEnvironment.checkResult
        (LookupStep.run (($segment).map (·.step)) $previous) $checkpoint = true := by decide +kernel))
      elabCommand (← `(theorem $chunkReplayed : LookupStep.run (($segment).map (·.step)) $previous = some $checkpoint :=
        LookupEnvironment.checkResult_sound $chunkChecked))
      elabCommand (← `(theorem $checkpointSound {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
        (values : GKRAddress → R) (holds : ∀ gate ∈ $native, gate.Holds hom challenges gamma values) :
        ($checkpoint).Sound values (NativeLookupLeaf.registryValue $registry hom challenges gamma values) :=
        NativeLookupBinding.replay_sound $segmentValid hom challenges gamma values holds
          ($previousSound hom challenges gamma values holds) $chunkReplayed))
      previous := checkpoint
      previousSound := checkpointSound
    let result := mkIdent (name.getId ++ `environment)
    let resultSound := mkIdent (name.getId ++ `environmentSound)
    elabCommand (← `(noncomputable def $result : LookupEnvironment := $previous))
    elabCommand (← `(theorem $resultSound {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (values : GKRAddress → R) (holds : ∀ gate ∈ $native, gate.Holds hom challenges gamma values) :
      ($result).Sound values (NativeLookupLeaf.registryValue $registry hom challenges gamma values) :=
      $previousSound hom challenges gamma values holds))
    for (kind, ports) in pair.circuit.global_output_map.entries do
      let rootName ← match kind with
        | .GenericLookup => pure (some "generic")
        | .Lookup16Bits => pure (some "range16")
        | .LookupTimestamps => pure (some "timestamp")
        | .PermutationProduct | .InitsAndTeardownsProduct => pure none
      if let some label := rootName then
        let output := mkIdent (name.getId ++ Name.mkSimple s!"{label}Output")
        let tree := mkIdent (name.getId ++ Name.mkSimple s!"{label}Tree")
        let present := mkIdent (name.getId ++ Name.mkSimple s!"{label}Present")
        let found := mkIdent (name.getId ++ Name.mkSimple s!"{label}Found")
        elabCommand (← `(noncomputable def $output : RationalPorts := $(← pairSyntax ports)))
        elabCommand (← `(noncomputable def $tree : LookupTree Nat :=
          (($result).pair $output).getD (.leaf 0)))
        elabCommand (← `(theorem $present : (($result).pair $output).isSome = true := by decide +kernel))
        elabCommand (← `(theorem $found : ($result).pair $output = some $tree :=
          option_eq_some_getD $present (.leaf 0)))
        let expected ← match kind with
          | .GenericLookup => pure (pair.circuit.num_generic_lookups + 1)
          | .Lookup16Bits => pure (pair.circuit.range_check_16_lookup_expressions.size + 1)
          | .LookupTimestamps => pure (pair.circuit.timestamp_range_check_lookup_expressions.size + 1)
          | _ => throwError "invalid rational output group"
        let cardinality := mkIdent (name.getId ++ Name.mkSimple s!"{label}OperandCount")
        elabCommand (← `(theorem $cardinality : ($tree).leaves.length = $(quote expected) := by decide +kernel))
        let oneSetup := mkIdent (name.getId ++ Name.mkSimple s!"{label}OneSetup")
        elabCommand (← `(theorem $oneSetup :
          (($tree).leaves.filter (fun index => (($registry)[index]?.map NativeLookupLeaf.isSetup).getD false)).length = 1 := by
          decide +kernel))
        let reduction := mkIdent (name.getId ++ Name.mkSimple s!"{label}Reduction")
        elabCommand (← `(theorem $reduction {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
          (values : GKRAddress → R) (holds : ∀ gate ∈ $native, gate.Holds hom challenges gamma values) :
          ($output).value values =
            (($tree).leaves.map (NativeLookupLeaf.registryValue $registry hom challenges gamma values)).sum :=
          (LookupEnvironment.pair_sound ($resultSound hom challenges gamma values holds) $found).trans
            (($tree).exact_sum (NativeLookupLeaf.registryValue $registry hom challenges gamma values))))

end Airbender.Compiler.NativeLookupImport
