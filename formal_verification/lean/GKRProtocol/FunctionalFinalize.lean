import GKRProtocol.FunctionalImport

namespace Airbender.Compiler.FunctionalFinalize
open Lean Elab Command
set_option warningAsError true

/-- Untrusted assembly selectors refer only to already reflected native data.
The concluding quantified theorems check complete list coverage in the kernel. -/
structure BaseIndex where
  affine : Nat
  gate : Nat
  deriving FromJson

structure Selectors where
  steps : Nat
  affine_steps : Array (Option Nat)
  «base» : Array BaseIndex
  lookup_steps : Array Nat
  product_steps : Array Nat
  deriving FromJson

private def memberName (owner : Ident) (stem : String) (index : Nat) : Ident :=
  mkIdent (owner.getId ++ Name.mkSimple s!"{stem}{index}")

private def fieldName (owner : Ident) (stem : String) : Ident :=
  mkIdent (owner.getId ++ Name.mkSimple stem)

private def predicateChecks (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(PredicateChecks.nil)
  for proof in proofs.reverse do result ← `(PredicateChecks.cons $proof $result)
  return result

syntax (name := finalizeCheckedFunctionalGraph) "finalize_checked_functional_graph " ident " selectors " str
  " lookup " ident " product " ident " base " ident : command

elab_rules : command
  | `(finalize_checked_functional_graph $name:ident selectors $selectorText:str
      lookup $lookupName:ident product $productName:ident base $baseName:ident) => do
    let data ← match Json.parse selectorText.getString >>= (fromJson? (α := Selectors)) with
      | .ok data => pure data | .error error => throwError "invalid functional proof selectors: {error}"
    let program := fieldName name "program"
    let isBase := fieldName name "isBase"
    let valid := fieldName name "valid"
    let mut validity ← `(FunctionalProgram.Valid.nil)
    for index in (List.range data.steps).reverse do
      let checked := memberName name "stepChecked" index
      let known := memberName name "known" index
      let step := memberName name "step" index
      validity ← `(FunctionalProgram.Valid.cons
        (FunctionalStep.check_sound (isBase := $isBase) (known := $known) (step := $step) $checked) $validity)
    elabCommand (← `(theorem $valid : ($program).Valid $isBase [] := $validity))
    let canonical := fieldName name "canonical"
    let stepHolds := fieldName name "canonical_step_holds"
    let baseHolds := fieldName name "canonical_base"
    elabCommand (← `(noncomputable def $canonical {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (baseValue : GKRAddress → Source.BaseField) : GKRAddress → R :=
      Functional.read $isBase (hom ∘ baseValue)
        (($program).execute hom challenges gamma $isBase (hom ∘ baseValue) (fun _ => 0))))
    elabCommand (← `(theorem $stepHolds {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (baseValue : GKRAddress → Source.BaseField) :
      ∀ step ∈ $program, step.Holds hom challenges gamma ($canonical hom challenges gamma baseValue) :=
      (FunctionalProgram.execute_sound $valid hom challenges gamma (hom ∘ baseValue) (fun _ => 0)).1))
    elabCommand (← `(theorem $baseHolds {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (baseValue : GKRAddress → Source.BaseField) (address : GKRAddress) (role : $isBase address = true) :
      $canonical hom challenges gamma baseValue address = hom (baseValue address) := by
      change (if $isBase address then hom (baseValue address) else _) = _
      exact if_pos role))
    let artifact := fieldName baseName "artifact"
    let bank := fieldName baseName "bank"
    let mut affineProofs := #[]
    for index in [:data.affine_steps.size] do
      let affine := memberName name "affine" index
      let result := memberName name "affineHolds" index
      let proof ← if let some stepIndex := data.affine_steps[index]! then
          let step := memberName name "step" stepIndex
          `(by
            have bridge (values : GKRAddress → R) (equation : ($step).Holds hom challenges gamma values) :
                ($affine).Holds hom challenges values := by
              exact equation (($step).get ⟨0, by decide⟩) (List.get_mem $step ⟨0, by decide⟩)
            exact bridge ($canonical hom challenges gamma baseValue)
              ($stepHolds hom challenges gamma baseValue $step
                (List.get_mem $program ⟨$(quote stepIndex), by decide⟩)))
        else do
          let some ordinal := data.base.findIdx? (fun binding => binding.affine == index)
            | throwError "base affine binding disappeared"
          let some binding := data.base[ordinal]? | throwError "base affine index is outside reflected list"
          let recipe := memberName name "baseRecipe" ordinal
          let output := memberName name "baseOutput" ordinal
          let ports := memberName name "basePortsChecked" ordinal
          let identity := memberName name "baseRelationChecked" ordinal
          let gate := memberName baseName "gate" binding.gate
          let gateChecked := memberName baseName "gateChecked" binding.gate
          `(NativeBaseRecipe.definition_of_gate $recipe $bank $isBase $output $gate $ports $identity
            $gateChecked hom challenges baseValue ($canonical hom challenges gamma baseValue)
            ($baseHolds hom challenges gamma baseValue)
            (arithmetic $gate (List.get_mem ($artifact).gates ⟨$(quote binding.gate), by decide⟩)))
      elabCommand (← `(theorem $result {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
        (baseValue : GKRAddress → Source.BaseField)
        (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (baseValue ∘ ($bank).address) = 0) :
        ($affine).Holds hom challenges ($canonical hom challenges gamma baseValue) := $proof))
      affineProofs := affineProofs.push (← `($result hom challenges gamma baseValue arithmetic))
    let definitions := fieldName name "definitions"
    let affines := fieldName name "canonical_affines"
    elabCommand (← `(theorem $affines {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (baseValue : GKRAddress → Source.BaseField)
      (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (baseValue ∘ ($bank).address) = 0) :
      ∀ definition ∈ $definitions, definition.Holds hom challenges ($canonical hom challenges gamma baseValue) :=
      PredicateChecks.all $(← predicateChecks affineProofs)))
    for (kind, owner, steps) in [("lookup", lookupName, data.lookup_steps), ("product", productName, data.product_steps)] do
      let mut proofs := #[]
      for (stepIndex, index) in steps.toList.zipIdx do
        let step := memberName name "step" stepIndex
        let gate := memberName owner "gate" index
        let result := memberName name (kind ++ "Holds") index
        let equation ← `($stepHolds hom challenges gamma baseValue $step
          (List.get_mem $program ⟨$(quote stepIndex), by decide⟩))
        let bridgeType ← if kind == "lookup" then `(($gate).Holds hom challenges gamma values)
          else `(($gate).Holds hom challenges values)
        let bridgeProof ← if kind == "product" && data.lookup_steps.contains stepIndex then
            `(by exact equation (($step).get ⟨0, by decide⟩) (List.get_mem $step ⟨0, by decide⟩))
          else `(($gate).functional_sound hom challenges gamma values equation)
        let proof ← `(by
          have bridge (values : GKRAddress → R) (equation : ($step).Holds hom challenges gamma values) :
              $bridgeType := $bridgeProof
          exact bridge ($canonical hom challenges gamma baseValue) $equation)
        let proposition ← if kind == "lookup" then
            `(($gate).Holds hom challenges gamma ($canonical hom challenges gamma baseValue))
          else `(($gate).Holds hom challenges ($canonical hom challenges gamma baseValue))
        elabCommand (← `(theorem $result {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
          (baseValue : GKRAddress → Source.BaseField) : $proposition := $proof))
        proofs := proofs.push (← `($result hom challenges gamma baseValue))
      let result := fieldName name ("canonical_" ++ kind ++ "s")
      let gates := fieldName owner "gates"
      let proposition ← if kind == "lookup" then
          `(∀ gate ∈ $gates, gate.Holds hom challenges gamma ($canonical hom challenges gamma baseValue))
        else `(∀ gate ∈ $gates, gate.Holds hom challenges ($canonical hom challenges gamma baseValue))
      elabCommand (← `(theorem $result {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
        (baseValue : GKRAddress → Source.BaseField) : $proposition :=
        PredicateChecks.all $(← predicateChecks proofs)))
    let inputs := fieldName baseName "inputs"
    let inputBank := fieldName baseName "inputBank"
    let coordinates := fieldName baseName "inputCoordinates"
    let roundTrip := fieldName baseName "bankRoundTrip"
    let arithmeticExtends := fieldName baseName "full_arithmetic_extends"
    let lookups := fieldName name "canonical_lookups"
    let products := fieldName name "canonical_products"
    let lookupGates := fieldName lookupName "gates"
    let productGates := fieldName productName "gates"
    let extendsName := fieldName name "full_graph_extends"
    elabCommand (← `(theorem $extendsName {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (sourceValue : Fin ($inputs).length → Source.BaseField)
      (sourceHolds : Satisfies ($artifact).source sourceValue) (fallback : GKRAddress → Source.BaseField) :
      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
        (∀ wire, baseValue (($inputBank).address wire) = sourceValue wire) ∧
        (∀ gate ∈ ($artifact).gates, gate.expressionResidual (baseValue ∘ ($bank).address) = 0) ∧
        (∀ address, $isBase address = true → values address = hom (baseValue address)) ∧
        (∀ definition ∈ $definitions, definition.Holds hom challenges values) ∧
        (∀ gate ∈ $lookupGates, gate.Holds hom challenges gamma values) ∧
        (∀ gate ∈ $productGates, gate.Holds hom challenges values) := by
      let extended := ($artifact).translation.extend sourceValue
      let baseValue := ($bank).materialize extended fallback
      have arithmetic := $arithmeticExtends sourceValue sourceHolds
      have baseArithmetic := WireBank.materialize_gates $bank $roundTrip extended fallback
        ($artifact).gates arithmetic.2
      refine ⟨baseValue, $canonical hom challenges gamma baseValue, ?_, baseArithmetic,
        $baseHolds hom challenges gamma baseValue,
        $affines hom challenges gamma baseValue baseArithmetic,
        $lookups hom challenges gamma baseValue, $products hom challenges gamma baseValue⟩
      intro wire
      exact WireBank.materialize_source_input $bank $inputBank ($artifact).projection $coordinates
        $roundTrip sourceValue extended arithmetic.1 fallback wire))

end Airbender.Compiler.FunctionalFinalize
