import Airbender.Import.Blake2Worker

namespace Airbender.Import.Blake2Queries
open Lean Elab Command

private def constantSyntax (n : Int) : CommandElabM (TSyntax `term) := do
  let value ← if n ≥ 0 then `(Int.ofNat $(quote n.toNat)) else `(Int.negSucc $(quote (-n-1).toNat))
  `(_root_.Expression.const (Int.cast $value))

private partial def exprSyntax (e : Expr) : CommandElabM (TSyntax `term) := do
  match e with
  | .Constant c => constantSyntax (Artifact.signedCoefficient c)
  | .Var v => `(_root_.Expression.var ⟨$(quote v)⟩)
  | .Sum es => es.foldlM (fun acc e => do `(_root_.Expression.add $acc $(← exprSyntax e))) (← constantSyntax 0)
  | .Product es => es.foldlM (fun acc e => do `(_root_.Expression.mul $acc $(← exprSyntax e))) (← constantSyntax 1)

/-- Separate same-read query observables; the original complete worker intake is unchanged.
    Every observable is independently bound to those accepted native operations in Proofs. -/
elab "import_native_blake2_queries " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let c ← match Blake2Worker.parse source with | .ok c => pure c | .error e => throwError e
  let emit (suffix : String) (entries : Array (TSyntax `term)) (row : TSyntax `term) : CommandElabM Unit := do
    let target := mkIdent (name.getId.appendAfter suffix)
    elabCommand (← `(def $target {p : Nat} [Fact (Nat.Prime p)] : Vector $row $(quote entries.size) := #v[$[$entries],*]))
  let scalars ← c.ranges.mapM fun e => do
    match c.lookup e with | .ok e => exprSyntax e | .error e => throwError e
  emit "Scalars" scalars (← `(_root_.Expression (ZMod p)))
  for (start,count,suffix) in #[(0,30,"Clocks0"),(30,56,"Clocks1")] do
    let clocks ← (c.clocks.extract start (start+count)).mapM fun e => do
      match c.lookup e with | .ok e => exprSyntax e | .error e => throwError e
    emit suffix clocks (← `(_root_.Expression (ZMod p)))
  for (start,count,suffix) in #[(0,8,"Fixed0"),(8,64,"Fixed1"),(72,64,"Fixed2"),(136,64,"Fixed3"),(200,8,"Fixed4")] do
    let queries ← (c.queries.extract start (start+count)).mapM fun (inputs,id) => do
      let entries ← inputs.mapM fun e => do
        match c.lookup e with | .ok e => exprSyntax e | .error e => throwError e
      let tag ← constantSyntax id
      `(#v[$(entries[0]!),$(entries[1]!),$(entries[2]!),$tag])
    emit suffix queries (← `(Vector (_root_.Expression (ZMod p)) 4))
  let bytes := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $bytes : String := $(quote source)))

end Airbender.Import.Blake2Queries
