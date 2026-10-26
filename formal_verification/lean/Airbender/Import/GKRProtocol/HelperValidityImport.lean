import Airbender.Proofs.GKRProtocol.CanonicalSource
import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Import.GKRProtocol.HelperImport

namespace Airbender.Compiler.HelperValidityImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)

private def variableField (index : Nat) : CommandElabM (TSyntax `term) :=
  `(Source.MemoryField.input (.Variable $(quote index)))

private def originalWord (columns : Fixed 2 Nat) : CommandElabM (TSyntax `term) := do
  `(Source.MemoryWord.mk $(← variableField columns.values[0]!) $(← variableField columns.values[1]!))

private def checksSyntax (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(BoolChecks.nil)
  for proof in proofs.reverse do result ← `(BoolChecks.cons $proof $result)
  return result

syntax (name := importHelperValidity) "import_helper_validity " ident " from " str
  " base_model " ident " source_model " ident " history_model " ident " helper_model " ident
  " memory_model " ident " inputs " num : command

elab_rules : command
  | `(import_helper_validity $name:ident from $path:str base_model $baseName:ident source_model $sourceName:ident
      history_model $historyName:ident helper_model $helperName:ident memory_model $memoryName:ident inputs $arityNumber:num) => do
    let snapshot ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Source.Snapshot)) with
      | .ok snapshot => pure snapshot | .error error => throwError "{error}"
    let memory ← match Source.memoryRequests snapshot.semantic_inputs with
      | .ok memory => pure memory | .error error => throwError "{error}"
    let requests ← match Source.helperRequests snapshot.semantic_inputs with
      | .ok requests => pure requests | .error error => throwError "{error}"
    let placement := fieldName baseName "helperPlacement"
    let comparisons := fieldName sourceName "comparisons"
    let slots := fieldName sourceName "slots"
    let unique := fieldName sourceName "slotsUnique"
    let coordinates := fieldName sourceName "slotCoordinates"
    let fresh := fieldName sourceName "slotsFresh"
    let scope := fieldName sourceName "protectedScope"
    let sourceSplit := fieldName sourceName "sourceSplit"
    let protectedHolds := fieldName sourceName "protected_holds"
    let protectedPolys := fieldName sourceName "protectedPolynomials"
    let originals := fieldName sourceName "originals"
    let clock := fieldName sourceName "clock"
    let artifact := fieldName baseName "artifact"
    let historyCells := fieldName historyName "historyCells"
    let historyChecked := fieldName historyName "arithmeticChecked"
    let historyFields := fieldName historyName "historyFields"
    let historyZero := fieldName historyName "history_fields_zero"
    let fields := fieldName helperName "fields"
    let nativePlacement := fieldName helperName "placement"
    let nativeValues := fieldName helperName "sourceValues"
    let nativeBank := fieldName memoryName "bank"
    let inputBank := fieldName baseName "inputBank"
    let execute := fieldName name "execute"
    elabCommand (← `(noncomputable def $execute : Source.MemoryField := $(← variableField memory.execute)))
    let clockTerm ← match snapshot.semantic_inputs.executor_machine_state,
        snapshot.semantic_inputs.delegation_circuit_state with
      | some executor, none => `(Source.HelperClock.executor $(← originalWord executor.cycle_end_state.timestamp))
      | none, some delegation => `(Source.HelperClock.worker $(← originalWord delegation.invocation_timestamp) $execute)
      | _, _ => throwError "source helper validity has an ambiguous clock profile"
    let mut alignments := #[]
    for access in snapshot.semantic_inputs.register_and_indirect_accesses do
      let bits := access.indirects_alignment_log2.val
      if bits != 0 then
        let read := match access.register_access with | .Read value | .Write value _ => value
        alignments := alignments.push (← `(Source.HelperAlignment.mk $(quote (2 ^ bits))
          $(← variableField read.values[0]!)))
    let profile := fieldName name "profile"
    elabCommand (← `(noncomputable def $profile : Source.HelperProfile := ⟨$clockTerm, $comparisons, [$alignments,*]⟩))
    let fieldsMatch := fieldName name "fieldsMatch"
    elabCommand (← `(theorem $fieldsMatch : ($profile).fields = $fields := by
      run_tac
        Lean.Elab.Tactic.liftMetaTactic fun goal => Lean.Meta.withTransparency .all do
          goal.refl
          pure []))
    let protectedChecked := fieldName name "protectedChecked"
    elabCommand (← `(theorem $protectedChecked : ($profile).protectedFields.all (fun field =>
      equal (substitute (erasurePolynomials $historyCells) (field.polynomial ($placement).memory))
        (field.polynomial ($placement).memory)) = true := by decide +kernel))
    let borrowChecked := fieldName name "borrowChecked"
    elabCommand (← `(theorem $borrowChecked : ($fields).all (Source.HelperField.borrowCheck $placement $slots) = true := by decide +kernel))
    let transportChecked := fieldName name "transportChecked"
    let predicate ← `(fun field : Source.HelperField => field.transportCheck $placement $nativePlacement $inputBank $nativeBank)
    let mut transportProofs := #[]
    for index in [:requests.timestamps.size] do
      let checked := fieldName name s!"transportChecked{index}"
      elabCommand (← `(theorem $checked : ($predicate) (($fields).get ⟨$(quote index), by decide⟩) = true := by decide +kernel))
      transportProofs := transportProofs.push (← `($checked))
    elabCommand (← `(theorem $transportChecked : ($fields).all $predicate = true :=
      BoolChecks.all_true (predicate := $predicate) (items := $fields) $(← checksSyntax transportProofs)))
    let normalized := fieldName name "normalized"
    elabCommand (← `(noncomputable def $normalized (values : Fin $(quote arityNumber.getNat) → Source.BaseField) :=
      inactiveHistory $historyCells (($execute).value (($placement).memory.project values)) values))
    let normalizedValid := fieldName name "normalized_valid"
    elabCommand (← `(theorem $normalizedValid (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (valid : ($profile).ExecutionValid (($execute).value (($placement).memory.project values))
        (($placement).memory.project values)) :
      ($profile).Valid (($placement).memory.project ($normalized values)) := by
      apply Source.HelperProfile.canonicalized_valid $profile
        (($execute).value (($placement).memory.project values)) (($placement).memory.project values)
        (($placement).memory.project ($normalized values)) valid
      · intro field member
        unfold $normalized:ident inactiveHistory
        split
        · exact memoryField_erasure field ($placement).memory $historyCells
            (List.all_eq_true.mp $protectedChecked field member) values
        · rfl
      · intro active pair member
        simp only [$normalized:ident, inactiveHistory, if_neg active]
      · intro inactive pair member
        have lowMember : pair.1.low ∈ $historyFields :=
          List.mem_flatMap.mpr ⟨pair, member, by simp⟩
        have highMember : pair.1.high ∈ $historyFields :=
          List.mem_flatMap.mpr ⟨pair, member, by simp⟩
        simp only [$normalized:ident, inactiveHistory, if_pos inactive]
        exact ⟨$historyZero values pair.1.low lowMember, $historyZero values pair.1.high highMember⟩))
    let canonical := fieldName name "canonical"
    elabCommand (← `(noncomputable def $canonical (values : Fin $(quote arityNumber.getNat) → Source.BaseField) :=
      let normalized := $normalized values
      let helpers := Source.canonicalHelpers (($placement).memory.project normalized) $comparisons
      Source.assignBorrows $slots normalized (fun index => helpers.borrow index.val)))
    let membership := fieldName name "helper_membership"
    elabCommand (← `(theorem $membership (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (valid : ($profile).ExecutionValid (($execute).value (($placement).memory.project values))
        (($placement).memory.project values)) :
      ∀ field ∈ $fields, (field.value (($placement).project ($canonical values))).val < 524288 := by
      intro field member
      have same := Source.HelperField.assignCanonical_value field $placement $slots $unique $coordinates
        (List.all_eq_true.mp $borrowChecked field member) ($normalized values) $comparisons
      change (field.value (($placement).project (Source.assignBorrows $slots ($normalized values)
        (fun index => (Source.canonicalHelpers (($placement).memory.project ($normalized values)) $comparisons).borrow index.val)))).val < 524288
      rw [same]
      exact Source.HelperProfile.canonical_fields_valid $profile _ ($normalizedValid values valid) field
        (by rw [$fieldsMatch:ident]; exact member)))
    let nativeMembership := fieldName name "native_helper_membership"
    elabCommand (← `(theorem $nativeMembership (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (valid : ($profile).ExecutionValid (($execute).value (($placement).memory.project values))
        (($placement).memory.project values)) (base : GKRAddress → Source.BaseField)
      (inputAgreement : ∀ wire, base (($inputBank).address wire) = $canonical values wire) :
      ∀ field ∈ $fields, (field.value ($nativeValues base)).val < 524288 := by
      intro field member
      have same := Source.HelperField.transport_value field $placement $nativePlacement $inputBank $nativeBank
        (List.all_eq_true.mp $transportChecked field member) ($canonical values) base inputAgreement
      change (field.value (($nativePlacement).project (base ∘ ($nativeBank).address))).val < 524288
      rw [same]
      exact $membership values valid field member))
    let sourceHolds := fieldName name "source_holds"
    let frame := fieldName name "canonical_frame"
    elabCommand (← `(theorem $frame (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (index : Fin $(quote arityNumber.getNat)) (historyOutside : index ∉ $historyCells)
      (borrowOutside : ∀ borrow, $slots borrow ≠ index) : $canonical values index = values index := by
      exact (Source.assignBorrows_frame $slots ($normalized values)
        (fun index => (Source.canonicalHelpers (($placement).memory.project ($normalized values)) $comparisons).borrow index.val)
        index borrowOutside).trans
        (inactiveHistory_frame $historyCells (($execute).value (($placement).memory.project values)) values index historyOutside)))
    let activeFrame := fieldName name "canonical_active_frame"
    elabCommand (← `(theorem $activeFrame (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (active : ($execute).value (($placement).memory.project values) ≠ 0)
      (index : Fin $(quote arityNumber.getNat)) (borrowOutside : ∀ borrow, $slots borrow ≠ index) :
      $canonical values index = values index := by
      have assigned := Source.assignBorrows_frame $slots ($normalized values)
        (fun index => (Source.canonicalHelpers (($placement).memory.project ($normalized values)) $comparisons).borrow index.val)
        index borrowOutside
      change $canonical values index = values index
      exact assigned.trans (congrFun (inactiveHistory_active $historyCells _ active values) index)))
    elabCommand (← `(theorem $sourceHolds (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (original : Satisfies (($originals).map Expression.polynomial) values)
      (clockValid : Source.clockContract $clock (($placement).memory.project values)) :
      Satisfies ($artifact).source ($canonical values) := by
      have protectedResult := inactiveHistory_satisfies $historyCells $protectedPolys $historyChecked
        (($execute).value (($placement).memory.project values)) values ($protectedHolds values original clockValid)
      rw [$sourceSplit:ident]
      intro polynomial member
      rcases List.mem_append.mp member with protectedMember | borrowMember
      · exact (evaluate_assignBorrows polynomial $(quote snapshot.source.num_variables)
          (List.all_eq_true.mp $scope polynomial protectedMember) $slots $fresh ($normalized values)
          (fun index => (Source.canonicalHelpers (($placement).memory.project ($normalized values))
            $comparisons).borrow index.val)).trans
            (protectedResult polynomial protectedMember)
      · obtain ⟨assertion, included, same⟩ := List.mem_map.mp borrowMember
        rw [← same, Source.HelperAssertion.polynomial_value]
        exact Source.canonical_borrow_assertions $placement $slots $unique $coordinates
          ($normalized values) $comparisons assertion included))

end Airbender.Compiler.HelperValidityImport
