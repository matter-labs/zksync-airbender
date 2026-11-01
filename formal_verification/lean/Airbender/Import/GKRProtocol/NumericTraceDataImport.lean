import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.PackedNormalizationTrace

namespace Airbender.Compiler.NumericTraceDataImport
open Lean Elab Command
set_option warningAsError true

private def readField (value : Json) (name : String) : CommandElabM Json :=
  match value.getObjVal? name with
  | .ok field => pure field
  | .error message => throwError "{message}"

private def packedTerm (value : Json) : CommandElabM (TSyntax `term) := do
  let (count, number) ← match fromJson? (α := Nat × Nat) value with
    | .ok pair => pure pair
    | .error message => throwError "{message}"
  `(NumericPolynomialChecks.PackedNormalization.Packed.mk $(quote count) $(quote number))

private def rowTerm (value : Json) : CommandElabM (TSyntax `term) := do
  let expected ← packedTerm (← readField value "expected")
  let input ← packedTerm (← readField value "input")
  let steps ← match (← readField value "trace").getArr? with
    | .ok steps => pure steps
    | .error message => throwError "{message}"
  let trace ← steps.mapM fun step => do
    let (index, state) ← match fromJson? (α := Nat × Json) step with
      | .ok pair => pure pair
      | .error message => throwError "{message}"
    let state ← packedTerm state
    `((($(quote index) : Nat), $state))
  `(NumericPolynomialChecks.PackedNormalization.PolynomialRow.mk $expected $input [$trace,*])

/-- Read bounded leaves. The proved checker verifies every supplied state. -/
syntax "packed_normalization_rows " ident " from " str " [" str "]" : command
elab_rules : command
  | `(packed_normalization_rows $name:ident from $path:str [$entry:str]) => do
    let json ← match Json.parse (← IO.FS.readFile path.getString) with
      | .ok value => pure value
      | .error message => throwError "{message}"
    let values ← match (← readField json entry.getString).getArr? with
      | .ok values => pure values
      | .error message => throwError "{message}"
    withEnableInfoTree false do
      let mut leaves : Array (TSyntax `term) := #[]
      for index in [:max 1 ((values.size + 7) / 8)] do
        let leaf := mkIdent (name.getId ++ Name.mkSimple s!"leaf{index}")
        let rows ← (values.extract (8 * index) (min values.size (8 * (index + 1)))).mapM rowTerm
        elabCommand (← `(def $leaf : List NumericPolynomialChecks.PackedNormalization.PolynomialRow := [$rows,*]))
        leaves := leaves.push (← `($leaf))
      let rec append (start count : Nat) : CommandElabM (TSyntax `term) := do
        if count ≤ 1 then pure leaves[start]!
        else
          let middle := count / 2
          let left ← append start middle
          let right ← append (start + middle) (count - middle)
          `(List.append $left $right)
      termination_by count
      let all ← append 0 leaves.size
      elabCommand (← `(def $name : List NumericPolynomialChecks.PackedNormalization.PolynomialRow := $all))

end Airbender.Compiler.NumericTraceDataImport
