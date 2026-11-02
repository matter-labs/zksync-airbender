import Airbender.Import.GKRProtocol.FullArithmeticImport
import Airbender.Proofs.GKRProtocol.FullArithmeticChecks
import Lean.AddDecl

namespace Airbender.Compiler.FullArithmeticImport
open Lean Elab Command
set_option warningAsError true

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

/-- One closed check validates the complete arithmetic capture. -/
syntax (name := certifyFullArithmetic) "certify_full_compiler_arithmetic " ident
  " inputs " num " variables " num " sources " num " gates " num (" using " term)? : command

elab_rules : command
  | `(certify_full_compiler_arithmetic $name:ident inputs $inputNumber:num variables $variableNumber:num
      sources $sourceNumber:num gates $gateNumber:num $[using $supplied:term]?) => do
    let n := inputNumber.getNat
    let m := variableNumber.getNat
    let _sourceCount := sourceNumber.getNat
    let _gateCount := gateNumber.getNat
    unless 0 < n && n ≤ m do throwError "invalid full arithmetic capture dimensions"
    let artifact := mkIdent (name.getId ++ `artifact)
    let addresses := mkIdent (name.getId ++ `addresses)
    let certificateName := mkIdent (name.getId ++ `certificate)
    let checked := mkIdent (name.getId ++ `captureChecked)
    let proof ← match supplied with
      | some term => pure term
      | none => `(show FullArithmeticChecks.check $addresses $artifact $certificateName = true from by decide +kernel)
    kernelTheorem checked (← `(FullArithmeticChecks.check $addresses $artifact $certificateName = true)) proof

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
