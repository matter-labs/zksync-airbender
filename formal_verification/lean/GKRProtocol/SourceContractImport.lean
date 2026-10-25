import GKRProtocol.OriginalInputs
import GKRProtocol.FullArithmeticImport

namespace Airbender.Compiler.SourceContractImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def indexed (owner : Ident) (stem : String) (index : Nat) : Ident := fieldName owner s!"{stem}{index}"

private def inputSyntax (bound : Nat) : Source.LookupInput → CommandElabM (TSyntax `term)
  | .Variable index => do
      unless index < bound do throwError "source contract escapes original variables"
      `(Source.LookupInput.Variable $(quote index))
  | .Expression terms constant => do
      let terms ← terms.mapM fun (coefficient, index) => do
        unless index < bound do throwError "source contract expression escapes original variables"
        `((Coefficient.mk ⟨$(quote coefficient.raw.val), by decide⟩, $(quote index)))
      `(Source.LookupInput.Expression #[$terms,*] (Coefficient.mk ⟨$(quote constant.raw.val), by decide⟩))

private def fieldSyntax (bound : Nat) : Source.MemoryField → CommandElabM (TSyntax `term)
  | .input input => do `(Source.MemoryField.input $(← inputSyntax bound input))
  | .readTimestamp query limb => `(Source.MemoryField.readTimestamp $(quote query) ⟨$(quote limb.val), by decide⟩)
  | .initializationAddress limb => `(Source.MemoryField.initializationAddress ⟨$(quote limb.val), by decide⟩)
  | .teardownTimestamp query limb => `(Source.MemoryField.teardownTimestamp $(quote query) ⟨$(quote limb.val), by decide⟩)
  | .teardownValue query limb => `(Source.MemoryField.teardownValue $(quote query) ⟨$(quote limb.val), by decide⟩)
  | .constant value => `(Source.MemoryField.constant $(quote value))
  | .add left right => do `(Source.MemoryField.add $(← fieldSyntax bound left) $(← fieldSyntax bound right))
  | .scale scalar inner => do `(Source.MemoryField.scale $(quote scalar) $(← fieldSyntax bound inner))
  | .neg inner => do `(Source.MemoryField.neg $(← fieldSyntax bound inner))

private def wordSyntax (bound : Nat) (word : Source.MemoryWord) : CommandElabM (TSyntax `term) := do
  `(Source.MemoryWord.mk $(← fieldSyntax bound word.low) $(← fieldSyntax bound word.high))

syntax (name := importSourceContract) "import_compiler_source_contract " ident " from " str
  " source " str " base_model " ident " inputs " num : command

elab_rules : command
  | `(import_compiler_source_contract $name:ident from $pairPath:str source $sourcePath:str base_model $baseName:ident inputs $arityNumber:num) => do
    let pair ← match Json.parse (← IO.FS.readFile pairPath.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    let snapshot ← match Json.parse (← IO.FS.readFile sourcePath.getString) >>= (fromJson? (α := Source.Snapshot)) with
      | .ok snapshot => pure snapshot | .error error => throwError "{error}"
    unless pair.format_version == 1 && snapshot.format_version == 1 && pair.family == snapshot.family &&
        pair.cached == snapshot.cached do throwError "source contract belongs to a different compiler instance"
    let requests ← match Source.helperRequests snapshot.semantic_inputs with
      | .ok requests => pure requests | .error error => throwError "{error}"
    let originalCount := pair.source.num_variables
    let arity := arityNumber.getNat
    let artifact := fieldName baseName "artifact"
    let placement := fieldName baseName "helperPlacement"
    let borrowProjection := fieldName baseName "borrowProjection"
    let originals := fieldName name "originals"
    let mut expressions := #[]
    for index in [:pair.source.statements.size + pair.source.booleans.size] do
      expressions := expressions.push (← `($(indexed baseName "originalExpression" index)))
    elabCommand (← `(noncomputable def $originals : List (Expression $(quote arity) Source.BaseField) := [$expressions,*]))
    let clock := fieldName name "clock"
    let clockTerm ← match snapshot.semantic_inputs.executor_machine_state with
      | none => `(none)
      | some executor => do
          let initial := Source.MemoryWord.original executor.cycle_start_state.timestamp
          let final := Source.MemoryWord.original executor.cycle_end_state.timestamp
          `(some ($(← wordSyntax originalCount initial), $(← wordSyntax originalCount final)))
    elabCommand (← `(noncomputable def $clock : Option (Source.MemoryWord × Source.MemoryWord) := $clockTerm))
    let comparisons := fieldName name "comparisons"
    let comparisonTerms ← requests.comparisons.mapM fun (previous, current) => do
      `(($(← wordSyntax originalCount previous), $(← wordSyntax originalCount current)))
    elabCommand (← `(noncomputable def $comparisons : List (Source.MemoryWord × Source.MemoryWord) := [$comparisonTerms,*]))
    let slots := fieldName name "slots"
    let unique := fieldName name "slotsUnique"
    let coordinates := fieldName name "slotCoordinates"
    let fresh := fieldName name "slotsFresh"
    elabCommand (← `(def $slots : Fin ($borrowProjection).length → Fin $(quote arity) := ($borrowProjection).get))
    elabCommand (← `(theorem $unique : Function.Injective $slots := by decide +kernel))
    elabCommand (← `(theorem $coordinates : ∀ index, $slots index = ($placement).borrow index.val := by decide +kernel))
    elabCommand (← `(theorem $fresh : ∀ index, $(quote originalCount) ≤ ($slots index).val := by decide +kernel))
    let clockPolys := fieldName name "clockPolynomials"
    let protectedPolys := fieldName name "protectedPolynomials"
    let scope := fieldName name "protectedScope"
    let split := fieldName name "sourceSplit"
    let helperAssertions := fieldName baseName "helperAssertions"
    let helperSplit := fieldName name "helperSplit"
    elabCommand (← `(noncomputable def $clockPolys : List (Polynomial $(quote arity) Source.BaseField) :=
      (Source.clockAssertionsFor $clock).map (Source.HelperAssertion.polynomial $placement)))
    elabCommand (← `(noncomputable def $protectedPolys : List (Polynomial $(quote arity) Source.BaseField) :=
      ($originals).map Expression.polynomial ++ $clockPolys))
    elabCommand (← `(theorem $scope : ($protectedPolys).all (polynomialScopeCheck $(quote originalCount)) = true := by decide +kernel))
    elabCommand (← `(theorem $helperSplit : $helperAssertions = Source.clockAssertionsFor $clock ++
      Source.borrowAssertions ($borrowProjection).length := by
      run_tac
        Lean.Elab.Tactic.liftMetaTactic fun goal => Lean.Meta.withTransparency .all do
          goal.refl
          pure []))
    let sourcePolys ← expressions.mapM fun expression => `(($expression).polynomial)
    elabCommand (← `(theorem $split : ($artifact).source = $protectedPolys ++
      (Source.borrowAssertions ($borrowProjection).length).map (Source.HelperAssertion.polynomial $placement) := by
      change [$sourcePolys,*] ++ ($helperAssertions).map (Source.HelperAssertion.polynomial $placement) = _
      rw [$helperSplit:ident, List.map_append]
      change ($originals).map Expression.polynomial ++ ($clockPolys ++ _) =
        (($originals).map Expression.polynomial ++ $clockPolys) ++ _
      rw [List.append_assoc]))
    let protectedHolds := fieldName name "protected_holds"
    elabCommand (← `(theorem $protectedHolds (values : Fin $(quote arity) → Source.BaseField)
      (original : Satisfies (($originals).map Expression.polynomial) values)
      (clockValid : Source.clockContract $clock (($placement).memory.project values)) :
      Satisfies $protectedPolys values := by
      intro polynomial member
      rcases List.mem_append.mp member with originalMember | clockMember
      · exact original polynomial originalMember
      · obtain ⟨assertion, included, same⟩ := List.mem_map.mp clockMember
        rw [← same, Source.HelperAssertion.polynomial_value]
        exact Source.clock_assertions_complete $clock (($placement).project values) clockValid assertion included))
    let result := fieldName name "source_contract_extension"
    elabCommand (← `(theorem $result (values : Fin $(quote arity) → Source.BaseField)
      (original : Satisfies (($originals).map Expression.polynomial) values)
      (clockValid : Source.clockContract $clock (($placement).memory.project values)) :
      ∃ extended : Fin $(quote arity) → Source.BaseField,
        (∀ index, (∀ borrow, $slots borrow ≠ index) → extended index = values index) ∧
        Satisfies ($artifact).source extended := by
      let helpers := Source.canonicalHelpers (($placement).memory.project values) $comparisons
      let borrows := fun index : Fin ($borrowProjection).length => helpers.borrow index.val
      let extended := Source.assignBorrows $slots values borrows
      refine ⟨extended, fun index outside => Source.assignBorrows_frame $slots values borrows index outside, ?_⟩
      rw [$split:ident]
      intro polynomial member
      rcases List.mem_append.mp member with protectedMember | borrowMember
      · exact (evaluate_assignBorrows polynomial $(quote originalCount)
          (List.all_eq_true.mp $scope polynomial protectedMember) $slots $fresh values borrows).trans
            ($protectedHolds values original clockValid polynomial protectedMember)
      · obtain ⟨assertion, included, same⟩ := List.mem_map.mp borrowMember
        rw [← same, Source.HelperAssertion.polynomial_value]
        exact Source.canonical_borrow_assertions $placement $slots $unique $coordinates values $comparisons assertion included))

end Airbender.Compiler.SourceContractImport
