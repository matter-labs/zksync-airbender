import GKRProtocol.NativeProduct
import GKRProtocol.CacheImport

namespace Airbender.Compiler.NativeProductImport
open Lean Elab Command
set_option warningAsError true

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .InnerLayer layer index => `(GKRAddress.InnerLayer $(quote layer) $(quote index))
  | .Cached layer index => `(GKRAddress.Cached $(quote layer) $(quote index))
  | .Setup index => `(GKRAddress.Setup $(quote index))
  | .ScratchSpace _ => throwError "native product cannot read ScratchSpace"
  | .VirtualSetup kind => do
      let kind ← match kind with
        | .RangeCheck16Bits => `(VirtualSetupPoly.RangeCheck16Bits)
        | .RangeCheckTimestamp => `(VirtualSetupPoly.RangeCheckTimestamp)
        | .InitsAndTeardownsLow => `(VirtualSetupPoly.InitsAndTeardownsLow)
        | .InitsAndTeardownsHigh => `(VirtualSetupPoly.InitsAndTeardownsHigh)
      `(GKRAddress.VirtualSetup $kind)

private def inputSyntax (address : GKRAddress) : CommandElabM (TSyntax `term) := do
  `(AffineProgram.input (R := CacheCoefficient) $(← addressSyntax address))

private def memoryScaled (index : Nat) (payload : TSyntax `term) : CommandElabM (TSyntax `term) :=
  `(AffineProgram.scale (CacheCoefficient.memoryPower ⟨$(quote index), by decide⟩) $payload)

private def initPayload (circuit : Circuit) (state : InitsOrTeardownsTimestampAndValue)
    (setup : Fixed 2 GKRAddress) (setIndex side : Nat) : CommandElabM (TSyntax `term) := do
  let some bits := circuit.memory_layout.inits_and_teardowns_word_bits | throwError "initialization product has no word width"
  let log := Nat.log2 circuit.trace_len
  unless (bits.val == 2 || bits.val == 3) && 2 ^ log == circuit.trace_len && 16 ≤ log + bits.val do
    throwError "invalid native initialization address domain"
  let highOffset := setIndex * 2 ^ (log + bits.val - 16)
  unless highOffset < babyBearModulus do throwError "native initialization high-address offset is not canonical"
  let [low, high] := setup.values.toList | throwError "initialization setup width changed"
  let mut result ← `(AffineProgram.add (AffineProgram.constant (Address := GKRAddress) CacheCoefficient.memoryGamma)
    (AffineProgram.constant (CacheCoefficient.natural 1)))
  result ← `(AffineProgram.add $result $(← memoryScaled 0 (← inputSyntax low)))
  let highInput ← `(AffineProgram.add $(← inputSyntax high)
    (AffineProgram.constant (CacheCoefficient.natural $(quote highOffset))))
  result ← `(AffineProgram.add $result $(← memoryScaled 1 highInput))
  match state with
  | .Init => pure ()
  | .Teardown leftTimestamp leftValue rightTimestamp rightValue =>
      let timestamps := if side == 0 then leftTimestamp else rightTimestamp
      let values := if side == 0 then leftValue else rightValue
      for (offset, index) in (timestamps.values ++ values.values).toList.zipIdx do
        result ← `(AffineProgram.add $result $(← memoryScaled (index + 2) (← inputSyntax (.BaseLayerMemory offset))))
  return result

structure Pieces where
  native : TSyntax `term
  step : TSyntax `term
  leaves : Array (TSyntax `term)
  equalities : Nat
  data : ProductStep

private def single (output : GKRAddress) (payload : TSyntax `term) (index : Nat) : CommandElabM Pieces := do
  let address ← addressSyntax output
  return ⟨← `(NativeProductGate.single $address $payload), ← `(ProductStep.single $address $(quote index)),
    #[payload], 2, .single output index⟩

private def pair (output : GKRAddress) (left right : TSyntax `term) (index : Nat) : CommandElabM Pieces := do
  let address ← addressSyntax output
  return ⟨← `(NativeProductGate.pair $address $left $right), ← `(ProductStep.pair $address $(quote index) $(quote (index + 1))),
    #[left, right], 3, .pair output index (index + 1)⟩

def pieces (circuit : Circuit) (memoryCaches : Array GKRAddress) (index : Nat) :
    GKRRelation → CommandElabM (Option Pieces)
  | .InitialGrandProductFromCaches input output => do
      let [left, right] := input.values.toList | throwError "invalid cached memory pair"
      return some (← pair output (← inputSyntax left) (← inputSyntax right) index)
  | .InitialGrandProductWithoutCaches input output => do
      let [left, right] := input.values.toList | throwError "invalid uncached memory pair"
      return some (← pair output (← CacheImport.program (.MemoryTuple left))
        (← CacheImport.program (.MemoryTuple right)) index)
  | .MaterializeGrandProductTermExpression input output => do
      return some (← single output (← CacheImport.program (.MemoryTuple input)) index)
  | .CopyInExtensionField input output => do
      if memoryCaches.any (· == input) then return some (← single output (← inputSyntax input) index)
      let out ← addressSyntax output
      let source ← addressSyntax input
      return some ⟨← `(NativeProductGate.copy $out $source), ← `(ProductStep.copy $out $source), #[], 2, .copy output input⟩
  | .TrivialProduct input output => do
      let [left, right] := input.values.toList | throwError "invalid product input width"
      let out ← addressSyntax output
      let lhs ← addressSyntax left
      let rhs ← addressSyntax right
      return some ⟨← `(NativeProductGate.mul $out $lhs $rhs), ← `(ProductStep.mul $out $lhs $rhs), #[], 3, .mul output left right⟩
  | .MaskIntoIdentityProduct input predicate output => do
      let out ← addressSyntax output
      let source ← addressSyntax input
      let maskAddress ← addressSyntax predicate
      return some ⟨← `(NativeProductGate.mask $out $source $maskAddress),
        ← `(ProductStep.mask $out $source $maskAddress), #[], 3, .mask output input predicate⟩
  | .InitsOrTeardownsInitialPair state setup output setIndices => do
      let [left, right] := setIndices.values.toList | throwError "invalid initialization set indices"
      return some (← pair output (← initPayload circuit state setup left 0)
        (← initPayload circuit state setup right 1) index)
  | .UnbalancedGrandProductWithCache _ _ _ => throwError "retired unbalanced product consumer"
  | .EnforceConstraintsMaxQuadratic _ => throwError "retired batched arithmetic consumer"
  | .LookupPairFromCachedVectorInputs _ _ => throwError "retired cached-vector lookup consumer"
  | .LinearBaseFieldRelation _ _ | .MaxQuadratic _ _ _ | .EnforceSingleMaxQuadraticConstraint _ _ |
    .CopyInBaseField _ _ | .MaterializeSingleLookupInput _ _ _ | .MaterializedVectorLookupInput _ _ |
    .LookupPairFromBaseInputs _ _ _ | .LookupPairFromVectorInputs _ _ |
    .LookupPairFromMaterializedBaseInputs _ _ | .LookupPairFromMaterializedVectorInputs _ _ |
    .LookupFromBaseInputsWithSetup _ _ _ _ | .LookupFromVectorInputWithSetup _ _ _ |
    .LookupFromMaterializedBaseInputWithSetup _ _ _ | .LookupFromMaterializedVectorInputWithSetup _ _ _ |
    .LookupWithCachedDensAndSetup _ _ _ | .LookupWithDensAndSetupExpressions _ _ _ |
    .LookupUnbalancedPairWithMaterializedBaseInputs _ _ _ | .LookupUnbalancedPairWithMaterializedVectorInputs _ _ _ |
    .LookupUnbalancedPairWithVectorInputs _ _ _ | .AggregateLookupRationalPair _ _ => pure none

private def checksSyntax (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(PredicateChecks.nil)
  for proof in proofs.reverse do result ← `(PredicateChecks.cons $proof $result)
  return result

private def formulaSyntax : ProductFormula → CommandElabM (TSyntax `term)
  | .leaf index => `(ProductFormula.leaf $(quote index))
  | .mul left right => do `(ProductFormula.mul $(← formulaSyntax left) $(← formulaSyntax right))
  | .mask address input => do `(ProductFormula.mask $(← addressSyntax address) $(← formulaSyntax input))

private def environmentSyntax (environment : ProductEnvironment) : CommandElabM (TSyntax `term) := do
  let entries ← environment.toArray.mapM fun (address, formula) => do
    `(($(← addressSyntax address), $(← formulaSyntax formula)))
  `([$entries,*])

private def plainTree : ProductFormula → Option (ProductTree Nat)
  | .leaf index => some (.leaf index)
  | .mul left right => do return .mul (← plainTree left) (← plainTree right)
  | .mask _ _ => none

private def treeSyntax : ProductTree Nat → CommandElabM (TSyntax `term)
  | .leaf index => `(ProductTree.leaf $(quote index))
  | .mul left right => do `(ProductTree.mul $(← treeSyntax left) $(← treeSyntax right))

syntax (name := importNativeProducts) "import_native_products " ident " from " str : command

elab_rules : command
  | `(import_native_products $name:ident from $path:str) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    unless pair.format_version == 1 do throwError "unsupported native product capture"
    let memoryCaches := pair.circuit.layers.flatMap fun layer => layer.cached_relations.filterMap fun (address, relation) =>
      match relation with | .MemoryTuple _ => some address | _ => none
    let mut gates : Array (TSyntax `term) := #[]
    let mut leaves : Array (TSyntax `term) := #[]
    let mut bindings : Array (TSyntax `term) := #[]
    let mut proofs : Array (TSyntax `term) := #[]
    let mut data : Array ProductStep := #[]
    for layer in pair.circuit.layers do
      for gate in layer.gates ++ layer.gates_with_external_connections do
        if let some description ← pieces pair.circuit memoryCaches leaves.size gate.enforced_relation then
          let raw := mkIdent (name.getId ++ Name.mkSimple s!"gate{gates.size}")
          let binding := mkIdent (name.getId ++ Name.mkSimple s!"binding{bindings.size}")
          elabCommand (← `(noncomputable def $raw : NativeProductGate := $(description.native)))
          elabCommand (← `(def $binding : NativeProductBinding := ⟨$(quote gates.size), $(description.step)⟩))
          gates := gates.push (← `($raw))
          bindings := bindings.push (← `($binding))
          data := data.push description.data
          for leaf in description.leaves do
            let leafName := mkIdent (name.getId ++ Name.mkSimple s!"leaf{leaves.size}")
            elabCommand (← `(noncomputable def $leafName : LookupPayload := $leaf))
            leaves := leaves.push (← `($leafName))
          proofs := proofs.push (← if description.equalities == 2 then `(⟨rfl, rfl⟩) else `(⟨rfl, rfl, rfl⟩))
    let native := mkIdent (name.getId ++ `gates)
    let registry := mkIdent (name.getId ++ `registry)
    let schedule := mkIdent (name.getId ++ `bindings)
    let valid := mkIdent (name.getId ++ `valid)
    elabCommand (← `(noncomputable def $native : List NativeProductGate := [$gates,*]))
    elabCommand (← `(noncomputable def $registry : List LookupPayload := [$leaves,*]))
    elabCommand (← `(def $schedule : List NativeProductBinding := [$bindings,*]))
    elabCommand (← `(theorem $valid : ∀ binding ∈ $schedule, binding.Valid $registry $native :=
      PredicateChecks.all $(← checksSyntax proofs)))
    let initial := mkIdent (name.getId ++ `environment0)
    let initialSound := mkIdent (name.getId ++ `environmentSound0)
    elabCommand (← `(def $initial : ProductEnvironment := []))
    elabCommand (← `(theorem $initialSound {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R)
      (_holds : ∀ gate ∈ $native, gate.Holds hom challenges values) :
      ProductEnvironment.Sound $initial values (productRegistryValue $registry hom challenges values) := by
      intro address formula member
      cases member))
    let mut previous := initial
    let mut previousSound := initialSound
    let mut environment : ProductEnvironment := []
    for block in [:(bindings.size + 31) / 32] do
      let first := block * 32
      let last := min (first + 32) bindings.size
      let segment := mkIdent (name.getId ++ Name.mkSimple s!"chunk{first}")
      let segmentValid := mkIdent (name.getId ++ Name.mkSimple s!"chunkValid{first}")
      let selected := bindings.extract first last
      let selectedProofs := proofs.extract first last
      elabCommand (← `(def $segment : List NativeProductBinding := [$selected,*]))
      elabCommand (← `(theorem $segmentValid : ∀ binding ∈ $segment, binding.Valid $registry $native :=
        PredicateChecks.all $(← checksSyntax selectedProofs)))
      let some next := ProductStep.run (data.extract first last).toList environment
        | throwError "actual native product trace fails at {first}..{last}"
      environment := next
      let checkpoint := mkIdent (name.getId ++ Name.mkSimple s!"environment{last}")
      let checkpointSound := mkIdent (name.getId ++ Name.mkSimple s!"environmentSound{last}")
      let replayed := mkIdent (name.getId ++ Name.mkSimple s!"chunkReplayed{first}")
      elabCommand (← `(def $checkpoint : ProductEnvironment := $(← environmentSyntax environment)))
      elabCommand (← `(theorem $replayed : ProductStep.run (($segment).map (·.step)) $previous = some $checkpoint := by rfl))
      elabCommand (← `(theorem $checkpointSound {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R)
        (holds : ∀ gate ∈ $native, gate.Holds hom challenges values) :
        ProductEnvironment.Sound $checkpoint values (productRegistryValue $registry hom challenges values) :=
        NativeProductBinding.replay_sound $segmentValid hom challenges values holds
          ($previousSound hom challenges values holds) $replayed))
      previous := checkpoint
      previousSound := checkpointSound
    for (kind, outputs) in pair.circuit.global_output_map.entries do
      let some stem := (match kind with | .PermutationProduct => some "memory" | .InitsAndTeardownsProduct => some "initialization" | _ => none)
        | continue
      unless outputs.size == 2 do throwError "native product output group has wrong width"
      for (output, side) in outputs.toList.zipIdx do
        let label := stem ++ if side == 0 then "Read" else "Write"
        let some formula := environment.find output | throwError "native product output has no checked reduction"
        let root := mkIdent (name.getId ++ Name.mkSimple s!"{label}Formula")
        let found := mkIdent (name.getId ++ Name.mkSimple s!"{label}Found")
        let result := mkIdent (name.getId ++ Name.mkSimple s!"{label}Reduction")
        elabCommand (← `(def $root : ProductFormula := $(← formulaSyntax formula)))
        elabCommand (← `(theorem $found : ($previous).find $(← addressSyntax output) = some $root := by rfl))
        elabCommand (← `(theorem $result {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R)
          (holds : ∀ gate ∈ $native, gate.Holds hom challenges values) :
          values $(← addressSyntax output) = ($root).value values (productRegistryValue $registry hom challenges values) :=
          $previousSound hom challenges values holds _ _ (ProductEnvironment.find_member $found)))
        let (predicate, tree) ← if stem == "memory" then
          match formula with
          | .mask predicate input => match plainTree input with
            | some tree => pure (some predicate, tree)
            | none => throwError "native RAM root contains an unexpected nested mask"
          | _ => throwError "native RAM root has no final execution mask"
        else match plainTree formula with
          | some tree => pure (none, tree)
          | none => throwError "native initialization root contains an unexpected mask"
        let productTree := mkIdent (name.getId ++ Name.mkSimple s!"{label}Product")
        let shape := mkIdent (name.getId ++ Name.mkSimple s!"{label}Shape")
        let cardinality := mkIdent (name.getId ++ Name.mkSimple s!"{label}OperandCount")
        let expected := if stem == "memory" then pair.circuit.memory_layout.ram_access_sets.size + 1
          else pair.circuit.memory_layout.teardown_sets.size
        elabCommand (← `(def $productTree : ProductTree Nat := $(← treeSyntax tree)))
        elabCommand (← `(theorem $cardinality : ($productTree).leaves.length = $(quote expected) := by decide +kernel))
        let body ← match predicate with
          | some address => `(ProductFormula.mask $(← addressSyntax address) (ProductFormula.ofTree $productTree))
          | none => `(ProductFormula.ofTree $productTree)
        elabCommand (← `(theorem $shape : $root = $body := by rfl))
        let productResult := mkIdent (name.getId ++ Name.mkSimple s!"{label}ProductReduction")
        let expectedValue ← match predicate with
          | some address => `(maskProduct (values $(← addressSyntax address))
              ((($productTree).leaves.map (productRegistryValue $registry hom challenges values)).prod))
          | none => `((($productTree).leaves.map (productRegistryValue $registry hom challenges values)).prod)
        elabCommand (← `(theorem $productResult {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R)
          (holds : ∀ gate ∈ $native, gate.Holds hom challenges values) :
          values $(← addressSyntax output) = $expectedValue := by
          have reduced := $result hom challenges values holds
          rw [$shape:ident] at reduced
          simpa only [ProductFormula.value, ProductFormula.ofTree_value, ProductTree.product] using reduced))

end Airbender.Compiler.NativeProductImport
