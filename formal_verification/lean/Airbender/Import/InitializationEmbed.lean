import Airbender.Import.Initialization

namespace Airbender.Initialization.Embed
open Lean Elab Command
set_option warningAsError true

private def portSyntax (wire : Port) : CommandElabM (TSyntax `term) :=
  `(Airbender.Initialization.Port.mk $(quote wire.layer) $(quote wire.offset))

private def columnsSyntax (columns : Columns) : CommandElabM (TSyntax `term) :=
  `(Airbender.Initialization.Columns.mk $(quote columns.timeLo) $(quote columns.timeHi)
    $(quote columns.valueLo) $(quote columns.valueHi))

private def leafSyntax (leaf : Leaf) : CommandElabM (TSyntax `term) := do
  let phase ← match leaf.phase with
    | .initial => `(Airbender.Initialization.Phase.initial)
    | .terminal => `(Airbender.Initialization.Phase.terminal)
  `(Airbender.Initialization.Leaf.mk $phase $(quote leaf.set) $(← columnsSyntax leaf.columns))

private def gateSyntax : Gate → CommandElabM (TSyntax `term)
  | .pair output left right => do
      `(Airbender.Initialization.Gate.pair $(← portSyntax output)
        $(← leafSyntax left) $(← leafSyntax right))
  | .product output left right => do
      `(Airbender.Initialization.Gate.product $(← portSyntax output)
        $(← portSyntax left) $(← portSyntax right))
  | .copy output input => do
      `(Airbender.Initialization.Gate.copy $(← portSyntax output) $(← portSyntax input))

private partial def treeSyntax : Tree → CommandElabM (TSyntax `term)
  | .pair output left right => do
      `(Airbender.Initialization.Tree.pair $(← portSyntax output)
        $(← leafSyntax left) $(← leafSyntax right))
  | .product output left right => do
      `(Airbender.Initialization.Tree.product $(← portSyntax output)
        $(← treeSyntax left) $(← treeSyntax right))
  | .copy output input => do
      `(Airbender.Initialization.Tree.copy $(← portSyntax output) $(← treeSyntax input))

private def artifactSyntax (artifact : Artifact) : CommandElabM (TSyntax `term) := do
  let columns ← artifact.layout.columns.mapM columnsSyntax
  let gates ← artifact.gates.mapM gateSyntax
  let layout := artifact.layout
  let layout ← `(Airbender.Initialization.Layout.mk $(quote layout.rows)
    $(quote layout.wordBits) $(quote layout.highOffset) $(quote layout.stride)
    $(quote layout.slots) $(quote layout.memoryWidth) #[$[$columns],*])
  `(Airbender.Initialization.Artifact.mk $layout #[$[$gates],*]
    $(← treeSyntax artifact.terminal) $(← treeSyntax artifact.initial) $(quote artifact.sourceBytes))

private def load (path : String) (flavor : Import.Flavor) : CommandElabM Artifact := do
  let source ← IO.FS.readFile path
  match Import.parse flavor source with
  | .ok artifact => pure artifact
  | .error error => throwError "initialization import failed: {error}"

elab "import_ram_initialization " name:ident " from " path:str
    inline:(" unified_inline")? : command => do
  let artifact ← load path.getString (if inline.isSome then .unified else .standalone)
  elabCommand (← `(def $name : Airbender.Initialization.Artifact := $(← artifactSyntax artifact)))

private partial def wiringSyntax : Tree → CommandElabM (TSyntax `term)
  | .pair _ _ _ => `(Airbender.Initialization.Tree.Follows.pair (by decide +kernel))
  | .product _ left right => do
      `(Airbender.Initialization.Tree.Follows.product (by decide +kernel)
        $(← wiringSyntax left) $(← wiringSyntax right))
  | .copy _ input => do
      `(Airbender.Initialization.Tree.Follows.copy (by decide +kernel) $(← wiringSyntax input))

/-- Proof implementation only: emitted constructor terms are checked against
    the separately imported data, so no expected wiring is an assumption. -/
elab "prove_ram_initialization_wiring " terminal:ident initial:ident
    " for " data:ident " from " path:str inline:(" unified_inline")? : command => do
  let artifact ← load path.getString (if inline.isSome then .unified else .standalone)
  let terminalProof ← wiringSyntax artifact.terminal
  let initialProof ← wiringSyntax artifact.initial
  elabCommand (← `(theorem $terminal :
    Airbender.Initialization.Tree.Follows ($data).gates ($data).terminal := $terminalProof))
  elabCommand (← `(theorem $initial :
    Airbender.Initialization.Tree.Follows ($data).gates ($data).initial := $initialProof))

end Airbender.Initialization.Embed
