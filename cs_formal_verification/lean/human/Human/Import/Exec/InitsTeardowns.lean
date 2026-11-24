module
public import Human.Import.Transcribe
public meta import Human.Import.Transcribe
public import Human.Import.InitsTeardownsLayout
public meta import Human.Import.InitsTeardownsLayout
public import Human.Helpers.Memory.InitsTeardownsColumns
public meta import Human.Helpers.Memory.InitsTeardownsColumns
public import Lean
public meta import Lean

public meta section

/-! No need to review: behaviour is fixed by `StandaloneImportClaim` and `UnifiedImportClaim`
(`Human/Circuits/InitsTeardowns/Artifact.lean`, `UnifiedArtifact.lean`).

`import_inits_teardowns name from circuit [standalone]` emits the inits/teardowns layout of the transcribed
artifact `circuit` (`Circuit.initsTeardownsLayout`, `InitsTeardownsLayout.lean`) as a literal term. -/

namespace Airbender
open Lean Elab Command

elab "import_inits_teardowns " name:ident " from " circuit:ident standalone:(" standalone")? : command => do
  let circuitName ← liftCoreM <| realizeGlobalConstNoOverload circuit
  let some (.lit (.strVal source)) := (← getConstInfo (circuitName.appendAfter "SourceBytes")).value?
    | throwError "{circuit} is not a transcribed circuit"
  let c ← match parseCircuit source with
    | .ok c => pure c
    | .error e => throwError "circuit import failed: {e}"
  let layout ← match c.initsTeardownsLayout standalone.isSome with
    | .ok layout => pure layout
    | .error e => throwError "inits/teardowns import failed: {e}"
  let pairSyntax := fun (columns : Vector Nat 2) =>
    `(#v[$(quote columns[0]), $(quote columns[1])])
  let setTerms ← layout.sets.toList.mapM fun set => do
    `(Airbender.InitsTeardowns.TeardownSet.mk $(← pairSyntax set.value) $(← pairSyntax set.timestamp))
  let setTerms := setTerms.toArray
  elabCommand (← `(def $name : Airbender.InitsTeardowns.Layout :=
    ⟨$(quote layout.traceLog), $(quote layout.wordBits), #[$[$setTerms],*]⟩))

end Airbender
