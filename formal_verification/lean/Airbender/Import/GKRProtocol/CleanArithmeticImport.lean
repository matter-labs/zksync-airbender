import Airbender.Import.Coefficients
import Airbender.Proofs.BabyBear
import Airbender.Proofs.GKRProtocol.CleanArithmetic
import Airbender.Proofs.GKRProtocol.CleanPlacementChecks
import Airbender.Proofs.GKRProtocol.CleanIdealChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Import.GKRProtocol.FullArithmeticImport
import Airbender.Proofs.GKRProtocol.NativeLookup

namespace Airbender.Compiler.CleanArithmeticImport
open Lean Elab Command
set_option warningAsError true

structure Selectors where
  format_version : Nat
  witnesses : Array Import.EncodedCombination
  deriving FromJson

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)

private def emitChecked (command : Syntax) : CommandElabM Unit := withEnableInfoTree false do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

private def checksSyntax (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(BoolChecks.nil)
  for proof in proofs.reverse do result ← `(BoolChecks.cons $proof $result)
  return result

private partial def collectVariables : Expr → List Nat
  | .Constant _ => []
  | .Var index => [index]
  | .Sum expressions | .Product expressions => expressions.toList.flatMap collectVariables

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .InnerLayer layer index => `(GKRAddress.InnerLayer $(quote layer) $(quote index))
  | .Cached layer index => `(GKRAddress.Cached $(quote layer) $(quote index))
  | .Setup index => `(GKRAddress.Setup $(quote index))
  | _ => throwError "post-compiler logical variable has a non-column placement"

private def constantSyntax (value : Int) : CommandElabM (TSyntax `term) := do
  let literal ← if value ≥ 0 then `(Int.ofNat $(quote value.toNat))
    else `(Int.negSucc $(quote (-value - 1).toNat))
  `(_root_.Expression.const (Int.cast $literal : Source.BaseField))

private partial def expressionSyntax : Expr → CommandElabM (TSyntax `term)
  | .Constant value => constantSyntax (Artifact.signedCoefficient value)
  | .Var index => `(_root_.Expression.var ⟨$(quote index)⟩)
  | .Sum expressions => do expressions.foldlM (fun previous expression => do
      `(_root_.Expression.add $previous $(← expressionSyntax expression))) (← constantSyntax 0)
  | .Product expressions => do expressions.foldlM (fun previous expression => do
      `(_root_.Expression.mul $previous $(← expressionSyntax expression))) (← constantSyntax 1)

private def statementSyntax : StructuredStatement → CommandElabM (TSyntax `term)
  | .AssertZero expression _ _ => expressionSyntax expression
  | .Define wire _ expression _ => do
      `(_root_.Expression.add (_root_.Expression.var ⟨$(quote wire)⟩)
        (_root_.Expression.mul $(← constantSyntax (-1)) $(← expressionSyntax expression)))

syntax (name := importCleanArithmetic) "import_clean_arithmetic " ident " from " str
  " selectors " str " base_model " ident " variables " num (" using " ident)? (" ideal_checks " ident)? : command

elab_rules : command
  | `(import_clean_arithmetic $name:ident from $path:str selectors $selectorText:str
      base_model $baseName:ident variables $arityNumber:num $[using $provided:ident]? $[ideal_checks $ideals:ident]?) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    let certificateData ← match Json.parse selectorText.getString >>= (fromJson? (α := Selectors)) with
      | .ok decoded => pure decoded | .error error => throwError "{error}"
    unless pair.format_version == 1 && certificateData.format_version == 1 &&
        certificateData.witnesses.size == pair.circuit.structured_statements.size do
      throwError "post-compiler arithmetic certificate has an incomplete assertion inventory"
    for statement in pair.circuit.structured_statements do
      let used := match statement with
        | .AssertZero expression _ _ => collectVariables expression
        | .Define output _ expression _ => output :: collectVariables expression
      unless used.all (fun index => pair.circuit.placement_data.entries.any (·.1 == index)) do
        throwError "retained Clean expression contains a logical variable without a native placement"
    emitChecked (← `(local instance : Field Source.BaseField := ZMod.instField _))
    emitChecked (← `(local instance : DecidableEq Source.BaseField := ZMod.decidableEq _))
    let bank := fieldName baseName "bank"
    let artifact := fieldName baseName "artifact"
    let gatesChecked := fieldName baseName "gatesChecked"
    let relations := fieldName name "relations"
    let placement := fieldName name "placement"
    let placementKeys := fieldName name "placementKeys"
    let placementAddresses := fieldName name "placementAddresses"
    let placementsRange := fieldName name "placementsRange"
    let placementsUnique := fieldName name "placementsUnique"
    let placementsInBank := fieldName name "placementsInBank"
    let environment := fieldName name "environment"
    emitChecked (← `(noncomputable def $relations : List (Polynomial $(quote arityNumber.getNat) Source.BaseField) :=
      ($artifact).gates.map ArithmeticGate.inputResidual))
    let placementEntries := pair.circuit.placement_data.entries.qsort (fun first second => decide (first.1 < second.1))
    let mappings ← placementEntries.mapM fun (index, address) => do
      `(($(quote index), ($bank).placement $(← addressSyntax address)))
    let keys : Array (TSyntax `term) := placementEntries.map (quote ∘ Prod.fst)
    let addresses ← placementEntries.mapM (addressSyntax ∘ Prod.snd)
    emitChecked (← `(def $placementKeys : List Nat := [$keys,*]))
    emitChecked (← `(def $placementAddresses : List GKRAddress := [$addresses,*]))
    emitChecked (← `(theorem $placementsRange : $placementKeys = List.range $(quote placementEntries.size) := by rfl))
    emitChecked (← `(theorem $placementsUnique : ($placementKeys).Nodup := by
      rw [$placementsRange:ident]
      exact List.nodup_range))
    let inBankPredicate ← `(fun address : GKRAddress => decide (($bank).address (($bank).placement address) = address))
    if let some owner := provided then
      let sourcePlacements := fieldName owner "placements"
      let sourceChecked := fieldName owner "placementsInBank"
      let binding := fieldName name "placementsSourceBinding"
      emitChecked (← `(theorem $binding : $placementAddresses = $sourcePlacements := by rfl))
      emitChecked (← `(theorem $placementsInBank : ($placementAddresses).all $inBankPredicate = true :=
        (congrArg (fun items : List GKRAddress => items.all $inBankPredicate) $binding).trans $sourceChecked))
      for index in [:addresses.size] do
        let checked := fieldName name s!"placementInBank{index}"
        emitChecked (← `(theorem $checked : ($inBankPredicate) $(addresses[index]!) = true :=
          CleanPlacementChecks.all_lookup $inBankPredicate $placementAddresses $placementsInBank
            $(quote index) $(addresses[index]!) (by rfl)))
    else
      let mut inBankProofs := #[]
      for index in [:addresses.size] do
        let checked := fieldName name s!"placementInBank{index}"
        emitChecked (← `(theorem $checked : ($inBankPredicate) $(addresses[index]!) = true := by decide +kernel))
        inBankProofs := inBankProofs.push (← `($checked))
      emitChecked (← `(theorem $placementsInBank : ($placementAddresses).all $inBankPredicate = true :=
        BoolChecks.all_true (predicate := $inBankPredicate) (items := $placementAddresses) $(← checksSyntax inBankProofs)))
    emitChecked (← `(def $placement (index : Nat) : Fin $(quote arityNumber.getNat) :=
      (([$mappings,*] : List (Nat × Fin $(quote arityNumber.getNat))).lookup index).getD ⟨0, by decide⟩))
    emitChecked (← `(def $environment (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
      Environment Source.BaseField := ⟨fun index => base (($bank).address ($placement index)), data⟩))
    let relationsHold := fieldName name "relations_hold"
    emitChecked (← `(theorem $relationsHold (base : GKRAddress → Source.BaseField)
      (holds : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (base ∘ ($bank).address) = 0) :
      Satisfies $relations (base ∘ ($bank).address) := by
      intro polynomial member
      obtain ⟨gate, included, same⟩ := List.mem_map.mp member
      rw [← same, gate.checked_value (List.all_eq_true.mp $gatesChecked gate included)]
      exact holds gate included))
    let idealRelations := fieldName name "idealRelationsBinding"
    if let some owner := ideals then
      let capture := fieldName owner "capture"
      let countBinding := fieldName name "idealCountBinding"
      let scopeBinding := fieldName name "idealScopeLimitBinding"
      emitChecked (← `(numeric_data_binding $idealRelations :
        ($relations).map NumericPolynomialChecks.encode = ($capture).relations.toList))
      emitChecked (← `(numeric_data_binding $countBinding : ($capture).codes.size =
        $(quote pair.circuit.structured_statements.size)))
      emitChecked (← `(numeric_data_binding $scopeBinding : ($capture).scopeLimit =
        $(quote placementEntries.size)))
    let mut expressions := #[]
    let mut proofs := #[]
    let mut scopeProofs := #[]
    for (statement, index) in pair.circuit.structured_statements.toList.zipIdx do
      let expression := fieldName name s!"expression{index}"
      let witness := fieldName name s!"witness{index}"
      let checked := fieldName name s!"checked{index}"
      let preserved := fieldName name s!"preserved{index}"
      emitChecked (← `(noncomputable def $expression : _root_.Expression Source.BaseField := $(← statementSyntax statement)))
      let mut entries := #[]
      for (polynomial, relation) in certificateData.witnesses[index]! do
        let terms ← polynomial.mapM fun (coefficient, monomial) => do
          unless coefficient < babyBearModulus && monomial.all (· < arityNumber.getNat) do
            throwError "noncanonical coefficient or out-of-domain post-arithmetic witness"
          let wires ← monomial.mapM fun wire => `(⟨$(quote wire), by decide⟩)
          `((($(quote coefficient) : Source.BaseField), [$wires,*]))
        entries := entries.push (← `(([$terms,*], ⟨$(quote relation), by decide⟩)))
      emitChecked (← `(noncomputable def $witness : Combination $relations := [$entries,*]))
      if let some owner := ideals then
        let capture := fieldName owner "capture"
        let whole := fieldName owner "checked"
        let codeBinding := fieldName name s!"idealCodeBinding{index}"
        let witnessBinding := fieldName name s!"idealWitnessBinding{index}"
        let inputsBinding := fieldName name s!"idealInputsBinding{index}"
        emitChecked (← `(numeric_data_binding $codeBinding :
          CleanIdealChecks.encode $placement $expression = ($capture).codes.getD $(quote index) (.constant 0)))
        emitChecked (← `(numeric_data_binding $witnessBinding :
          NumericPolynomialChecks.encodeCombination $witness = ($capture).witnesses.getD $(quote index) []))
        emitChecked (← `(numeric_data_binding $inputsBinding :
          CleanExpression.inputs $expression = ($capture).inputs.getD $(quote index) []))
        emitChecked (← `(theorem $checked : equal (CleanExpression.polynomial $placement $expression)
          (combination $relations $witness) = true :=
          CleanIdealChecks.check_sound_at $placement $relations $expression $witness $capture $whole
            $(quote index) (by decide +kernel) $codeBinding $idealRelations $witnessBinding))
        scopeProofs := scopeProofs.push (← `(CleanIdealChecks.scope_at $expression $capture $whole
          $(quote index) (by decide +kernel) $inputsBinding))
      else
        emitChecked (← `(theorem $checked : equal (CleanExpression.polynomial $placement $expression)
          (combination $relations $witness) = true := by decide +kernel))
      emitChecked (← `(theorem $preserved (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
        (holds : Satisfies $relations (base ∘ ($bank).address)) :
        ($expression).eval ($environment base data) = 0 :=
        CleanExpression.of_combination_at $expression $placement $relations $witness $checked
          ($bank).address base data holds))
      expressions := expressions.push (← `($expression))
      proofs := proofs.push (← `($preserved))
    let allExpressions := fieldName name "expressions"
    emitChecked (← `(noncomputable def $allExpressions : List (_root_.Expression Source.BaseField) := [$expressions,*]))
    let scope := fieldName name "scopeChecked"
    if ideals.isSome then
      emitChecked (← `(theorem $scope : ($allExpressions).all (fun expression =>
        (CleanExpression.inputs expression).all (fun index => decide (index < $(quote placementEntries.size)))) = true :=
        BoolChecks.all_true (predicate := fun expression =>
          (CleanExpression.inputs expression).all (fun index => decide (index < $(quote placementEntries.size))))
          (items := $allExpressions) $(← checksSyntax scopeProofs)))
    else
      emitChecked (← `(theorem $scope : ($allExpressions).all (fun expression =>
        (CleanExpression.inputs expression).all (fun index => decide (index < $(quote placementEntries.size)))) = true := by decide +kernel))
    let preserved := fieldName name "arithmetic_preserved"
    let mut cases ← `(PredicateChecks.nil)
    for proof in proofs.reverse do cases ← `(PredicateChecks.cons ($proof base data holds) $cases)
    emitChecked (← `(theorem $preserved (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
      (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (base ∘ ($bank).address) = 0) :
      FlatOperation.ConstraintsHoldFlat ($environment base data) (($allExpressions).map FlatOperation.assert) := by
      have holds := $relationsHold base arithmetic
      exact CleanExpression.assertions_hold $allExpressions ($environment base data)
        (PredicateChecks.all $cases)))

end Airbender.Compiler.CleanArithmeticImport
