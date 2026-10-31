import Airbender.Import.GKRProtocol.FullArithmeticImport
import Airbender.Proofs.GKRProtocol.FullArithmeticChecks
import Lean.AddDecl

namespace Airbender.Compiler.FullArithmeticImport
open Lean Elab Command
set_option warningAsError true

private def boundedIndex (index bound : Nat) : CommandElabM (TSyntax `term) :=
  `((⟨$(quote index), by decide⟩ : Fin $(quote bound)))

/-- Elaborate each side alone. The kernel checks conversion to the original type. -/
private def kernelTheorem (name : TSyntax `ident) (statement proof : TSyntax `term) : CommandElabM Unit := do
  let type ← liftTermElabM do
    let value ← Term.elabType statement
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  let value ← liftTermElabM do
    let value ← Term.elabTerm proof none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  let fullName := (← getCurrNamespace) ++ name.getId
  liftCoreM <| addDecl (.thmDecl {name := fullName, levelParams := [], type, value})

private def closedTerm (term : TSyntax `term) : CommandElabM Lean.Expr := liftTermElabM do
  let value ← Term.elabTerm term none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

private def kernelInstance (name : TSyntax `ident) (type value : Lean.Expr) : CommandElabM Unit := do
  let fullName := (← getCurrNamespace) ++ name.getId
  liftCoreM <| addDecl (.thmDecl {name := fullName, levelParams := [], type, value})

/-- One closed check supplies every original finite-case declaration. -/
syntax (name := certifyFullArithmetic) "certify_full_compiler_arithmetic " ident
  " inputs " num " variables " num " sources " num " gates " num (" using " term)? : command

elab_rules : command
  | `(certify_full_compiler_arithmetic $name:ident inputs $inputNumber:num variables $variableNumber:num
      sources $sourceNumber:num gates $gateNumber:num $[using $supplied:term]?) => do
    let n := inputNumber.getNat
    let m := variableNumber.getNat
    let sourceCount := sourceNumber.getNat
    let gateCount := gateNumber.getNat
    unless 0 < n && n ≤ m do throwError "invalid full arithmetic capture dimensions"
    let artifact := mkIdent (name.getId ++ `artifact)
    let addresses := mkIdent (name.getId ++ `addresses)
    let certificateName := mkIdent (name.getId ++ `certificate)
    let checked := mkIdent (name.getId ++ `captureChecked)
    let proof ← match supplied with
      | some term => pure term
      | none => `(show FullArithmeticChecks.check $addresses $artifact $certificateName = true from by decide +kernel)
    kernelTheorem checked (← `(FullArithmeticChecks.check $addresses $artifact $certificateName = true)) proof
    -- Elaborate symbolic predicates and proof functions once. Each public
    -- instance uses expression application. The kernel checks the result.
    let uniqueType ← closedTerm (← `((fun (coordinate : Fin $(quote m)) => distinctAt $addresses coordinate = true)))
    let uniqueProof ← closedTerm (← `(FullArithmeticChecks.unique_at $addresses $artifact $certificateName $checked))
    let relationType ← closedTerm (← `((fun (gate : ArithmeticGate $(quote m) Source.BaseField)
        (coordinate : Fin $(quote gateCount)) => equal (substitute ($artifact).extension gate.inputResidual)
          (combination ($artifact).source (($certificateName).forward coordinate)) = true)))
    let relationProof ← closedTerm (← `(FullArithmeticChecks.relation_at $addresses $artifact $certificateName $checked))
    let gateType ← closedTerm (← `((fun (gate : ArithmeticGate $(quote m) Source.BaseField) => gate.check = true)))
    let gateProof ← closedTerm (← `(FullArithmeticChecks.gate_at $addresses $artifact $certificateName $checked))
    let sourceType ← closedTerm (← `((fun (coordinate : Fin $(quote sourceCount)) => equal
        (rename ($artifact).projection (($artifact).source.get coordinate))
        (combination ($artifact).translation.lowered (($certificateName).backward coordinate)) = true)))
    let sourceProof ← closedTerm (← `(FullArithmeticChecks.source_at_original $addresses $artifact $certificateName $checked))
    for index in [:m] do
      let conclusion := mkIdent (name.getId ++ Name.mkSimple s!"uniqueChecked{index}")
      let coordinate ← closedTerm (← boundedIndex index m)
      kernelInstance conclusion (mkApp uniqueType coordinate).headBeta (mkApp uniqueProof coordinate)
    for index in [:gateCount] do
      let conclusion := mkIdent (name.getId ++ Name.mkSimple s!"relationChecked{index}")
      let gate := mkConst ((← getCurrNamespace) ++ name.getId ++ Name.mkSimple s!"gate{index}")
      let coordinate ← closedTerm (← boundedIndex index gateCount)
      kernelInstance conclusion (mkApp2 relationType gate coordinate).headBeta (mkApp relationProof coordinate)
      let gateConclusion := mkIdent (name.getId ++ Name.mkSimple s!"gateChecked{index}")
      kernelInstance gateConclusion (mkApp gateType gate).headBeta (mkApp gateProof coordinate)
    for index in [:sourceCount] do
      let conclusion := mkIdent (name.getId ++ Name.mkSimple s!"sourceChecked{index}")
      let coordinate ← closedTerm (← boundedIndex index sourceCount)
      kernelInstance conclusion (mkApp sourceType coordinate).headBeta (mkApp sourceProof coordinate)

/-- Derive the original public adapter facts directly from the complete check. -/
syntax "finalize_checked_full_compiler_arithmetic " ident " inputs " num " variables " num : command
elab_rules : command
  | `(finalize_checked_full_compiler_arithmetic $name:ident inputs $inputNumber:num variables $variableNumber:num) => do
    let n := inputNumber.getNat
    let m := variableNumber.getNat
    let artifact := mkIdent (name.getId ++ `artifact)
    let addressesName := mkIdent (name.getId ++ `addresses)
    let bank := mkIdent (name.getId ++ `bank)
    let certificateName := mkIdent (name.getId ++ `certificate)
    let checked := mkIdent (name.getId ++ `captureChecked)
    let unique := mkIdent (name.getId ++ `addressesUnique)
    elabCommand (← `(theorem $unique : ($addressesName).Nodup :=
      (FullArithmeticChecks.check_sound $addressesName $artifact $certificateName $checked).1))
    let roundTrip := mkIdent (name.getId ++ `bankRoundTrip)
    elabCommand (← `(theorem $roundTrip (wire : Fin $(quote m)) : ($bank).placement (($bank).address wire) = wire :=
      WireBank.ofList_roundTrip $addressesName (by decide) $unique wire))
    let valid := mkIdent (name.getId ++ `valid)
    elabCommand (← `(theorem $valid : ($certificateName).Valid :=
      (FullArithmeticChecks.check_sound $addressesName $artifact $certificateName $checked).2.1))
    let gatesChecked := mkIdent (name.getId ++ `gatesChecked)
    elabCommand (← `(theorem $gatesChecked : ($artifact).gates.all ArithmeticGate.check = true :=
      (FullArithmeticChecks.check_sound $addressesName $artifact $certificateName $checked).2.2))
    let extendsName := mkIdent (name.getId ++ `full_arithmetic_extends)
    elabCommand (← `(theorem $extendsName (values : Fin $(quote n) → Source.BaseField)
      (holds : Satisfies ($artifact).source values) :
      (∀ wire, ($artifact).translation.extend values (($artifact).projection wire) = values wire) ∧
        (∀ gate ∈ ($artifact).gates, gate.expressionResidual (($artifact).translation.extend values) = 0) :=
      ArithmeticExtension.forward $artifact ($certificateName).forwardOnly (Certificate.forwardOnly_valid $valid) $gatesChecked holds))
    let preserved := mkIdent (name.getId ++ `full_arithmetic_preserved)
    elabCommand (← `(theorem $preserved (values : Fin $(quote m) → Source.BaseField)
      (holds : ∀ gate ∈ ($artifact).gates, gate.expressionResidual values = 0) :
      Satisfies ($artifact).source (values ∘ ($artifact).projection) :=
      ArithmeticExtension.backward $artifact $certificateName $valid $gatesChecked holds))
    let equivalent := mkIdent (name.getId ++ `full_arithmetic_equivalent)
    elabCommand (← `(theorem $equivalent (values : Fin $(quote n) → Source.BaseField) :
      Satisfies ($artifact).source values ↔ ∃ extended : Fin $(quote m) → Source.BaseField,
        (∀ wire, extended (($artifact).projection wire) = values wire) ∧
        (∀ gate ∈ ($artifact).gates, gate.expressionResidual extended = 0) :=
      ArithmeticExtension.equivalent $artifact $certificateName $valid $gatesChecked values))

end Airbender.Compiler.FullArithmeticImport
