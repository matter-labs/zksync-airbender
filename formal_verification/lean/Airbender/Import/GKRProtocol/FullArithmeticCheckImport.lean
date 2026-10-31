import Airbender.Import.GKRProtocol.FullArithmeticImport
import Airbender.Proofs.GKRProtocol.FullArithmeticChecks

namespace Airbender.Compiler.FullArithmeticImport
open Lean Elab Command
set_option warningAsError true

private def boundedIndex (index bound : Nat) : CommandElabM (TSyntax `term) :=
  `((⟨$(quote index), by decide⟩ : Fin $(quote bound)))

/-- One closed check supplies every original finite-case declaration. -/
syntax (name := certifyFullArithmetic) "certify_full_compiler_arithmetic " ident
  " inputs " num " variables " num " sources " num " gates " num : command

elab_rules : command
  | `(certify_full_compiler_arithmetic $name:ident inputs $inputNumber:num variables $variableNumber:num
      sources $sourceNumber:num gates $gateNumber:num) => do
    let n := inputNumber.getNat
    let m := variableNumber.getNat
    let sourceCount := sourceNumber.getNat
    let gateCount := gateNumber.getNat
    unless 0 < n && n ≤ m do throwError "invalid full arithmetic capture dimensions"
    let artifact := mkIdent (name.getId ++ `artifact)
    let addresses := mkIdent (name.getId ++ `addresses)
    let certificateName := mkIdent (name.getId ++ `certificate)
    let checked := mkIdent (name.getId ++ `captureChecked)
    elabCommand (← `(theorem $checked :
      FullArithmeticChecks.check $addresses $artifact $certificateName = true := by decide +kernel))
    for index in [:m] do
      let conclusion := mkIdent (name.getId ++ Name.mkSimple s!"uniqueChecked{index}")
      let coordinate ← boundedIndex index m
      elabCommand (← `(theorem $conclusion : distinctAt $addresses $coordinate = true :=
        FullArithmeticChecks.unique_at $addresses $artifact $certificateName $checked $coordinate))
    for index in [:gateCount] do
      let conclusion := mkIdent (name.getId ++ Name.mkSimple s!"relationChecked{index}")
      let gate := mkIdent (name.getId ++ Name.mkSimple s!"gate{index}")
      let coordinate ← boundedIndex index gateCount
      elabCommand (← `(theorem $conclusion : equal (substitute ($artifact).extension ($gate).inputResidual)
        (combination ($artifact).source (($certificateName).forward $coordinate)) = true :=
        FullArithmeticChecks.relation_at $addresses $artifact $certificateName $checked $coordinate))
      let gateConclusion := mkIdent (name.getId ++ Name.mkSimple s!"gateChecked{index}")
      elabCommand (← `(theorem $gateConclusion : ($gate).check = true :=
        FullArithmeticChecks.gate_at $addresses $artifact $certificateName $checked $coordinate))
    for index in [:sourceCount] do
      let conclusion := mkIdent (name.getId ++ Name.mkSimple s!"sourceChecked{index}")
      let coordinate ← boundedIndex index sourceCount
      elabCommand (← `(theorem $conclusion : equal
        (rename ($artifact).projection (($artifact).source.get $coordinate))
        (combination ($artifact).translation.lowered (($certificateName).backward $coordinate)) = true :=
        FullArithmeticChecks.source_at $addresses $artifact $certificateName $checked $coordinate))

end Airbender.Compiler.FullArithmeticImport
