import Airbender.Import.SetupEmbed

namespace Airbender.Setup
open Lean Elab Command

private def emitChecked (command : Syntax) : CommandElabM Unit := do
  -- Generated literal helpers need no editor hover trees. Kernel checking and
  -- diagnostics stay enabled for every ordinary declaration.
  withEnableInfoTree false (elabCommand command)
  if (← get).messages.hasErrors then throwAbortCommand

private partial def arraySyntax (values : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  if values.size ≤ 64 then return ← `(#[$values,*])
  let left ← arraySyntax (values.extract 0 (values.size / 2))
  let right ← arraySyntax (values.extract (values.size / 2) values.size)
  `(Array.append $left $right)

private partial def appendSyntax (values : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  if values.isEmpty then return ← `(#[])
  if values.size = 1 then return values[0]!
  let left ← appendSyntax (values.extract 0 (values.size / 2))
  let right ← appendSyntax (values.extract (values.size / 2) values.size)
  `(Array.append $left $right)

/-- Short constructors are selected only after comparing every parsed value;
otherwise emit the literal array. No table recipe replaces materialized data. -/
private def valuesSyntax (values : Array Nat) : CommandElabM (TSyntax `term) := do
  if let some first := values[0]? then
    if values.all (· == first) then return ← `(Array.replicate $(quote values.size) $(quote first))
    if (values.mapIdx fun index value => value == index).all id then return ← `(Array.range $(quote values.size))
    if (values.mapIdx fun index value => value == first + index).all id then
      return ← `(Array.ofFn (fun index : Fin $(quote values.size) => $(quote first) + index.val))
    if (values.mapIdx fun index value => value == (first + index) % values.size).all id then
      return ← `(Array.ofFn (fun index : Fin $(quote values.size) =>
        ($(quote first) + index.val) % $(quote values.size)))
  let literals : Array (TSyntax `term) := values.map quote
  arraySyntax literals

private def integerSyntax (value : Int) : CommandElabM (TSyntax `term) :=
  if value ≥ 0 then `(Int.ofNat $(quote value.toNat)) else `(Int.negSucc $(quote (-value - 1).toNat))

private def blockSyntax : Block → CommandElabM (TSyntax `term)
  | .affine length first step => do
      `(Airbender.Setup.Block.affine $(quote length) $(quote first) $(← integerSyntax step))
  | .dense values => do `(Airbender.Setup.Block.dense $(← valuesSyntax values))
  | .periodic repetitions stride values => do
      `(Airbender.Setup.Block.periodic $(quote repetitions) $(← integerSyntax stride) $(← valuesSyntax values))

private def emitColumn (owner : Ident) (stem : String) (column : Column) : CommandElabM (TSyntax `term) := do
  let mut chunks := #[]
  for chunk in [: (column.blocks.size + 127) / 128] do
    let name := mkIdent (owner.getId.appendAfter s!"{stem}Blocks{chunk}")
    let blocks ← (column.blocks.extract (chunk * 128) (min column.blocks.size ((chunk + 1) * 128))).mapM blockSyntax
    let literal ← arraySyntax blocks
    emitChecked (← `(def $name : Array Airbender.Setup.Block := $literal))
    chunks := chunks.push (← `($name))
  let name := mkIdent (owner.getId.appendAfter stem)
  let literal ← appendSyntax chunks
  emitChecked (← `(def $name : Airbender.Setup.Column := ⟨$literal⟩))
  `($name)

/-- Import whole physical setup columns in bounded literal declarations. The
parser, validation, source bytes and circuit binding match `import_setup`.
Array chunking changes elaboration size only, preserving every block in order. -/
elab "import_full_setup " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact | .error error => throwError "setup import failed: {error}"
  let mut columns := #[]
  for (column, index) in artifact.columns.toList.zipIdx do
    columns := columns.push (← emitColumn name s!"Column{index}" column)
  let range16 ← emitColumn name "Range16Column" artifact.range16
  let timestamp ← emitColumn name "TimestampColumn" artifact.timestamp_range
  let regions ← artifact.tables.mapM fun region =>
    `(Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length)
      $(quote region.width) $(quote region.key_columns))
  let program ← match artifact.program with
    | none => `(none)
    | some program => do
        let image ← emitColumn name "ImageColumn" program.image
        let text ← emitColumn name "TextColumn" program.text
        `(some (Airbender.Setup.Program.mk $(quote program.image_words) $image $(quote program.text_words) $text))
  emitChecked (← `(def $name : Airbender.Setup.Imported $(quote artifact.columns.size) :=
    Airbender.Setup.Imported.mk
      (Airbender.Setup.TableData.mk $(quote artifact.trace_len) 0 #v[$columns,*])
      (Airbender.Setup.TableData.mk $(quote artifact.trace_len) 0 #v[$range16])
      (Airbender.Setup.TableData.mk $(quote artifact.trace_len) 0 #v[$timestamp])
      #[$regions,*] $program))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  emitChecked (← `(def $sourceName : String := $(quote source)))
  let json ← match Json.parse source with
    | .ok json => pure json | .error error => throwError "setup import failed: {error}"
  let circuit ← match json.getObjVal? "circuit" with
    | .ok circuit => pure circuit.compress | .error error => throwError "setup import failed: {error}"
  let circuitName := mkIdent (name.getId.appendAfter "CircuitSource")
  emitChecked (← `(def $circuitName : String := $(quote circuit)))

end Airbender.Setup
