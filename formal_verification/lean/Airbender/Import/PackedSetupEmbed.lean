import Airbender.Import.SetupRegionEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupEquality

namespace Airbender.Compiler.PackedSetupImport
open Lean Elab Command Airbender.Setup Airbender.Compiler.PackedSetupEquality
set_option warningAsError true

private partial def literalCode (values : Array Nat) : CommandElabM (TSyntax `term) := do
  if values.size ≤ 64 then
    let payload ← Slices.packByteValues values
    return ← `(ArrayCode.literal $(quote values.size) $(quote payload))
  let left ← literalCode (values.extract 0 (values.size / 2))
  let right ← literalCode (values.extract (values.size / 2) values.size)
  `(ArrayCode.append $left $right)

private def arrayCode (values : Array Nat) (packed : Bool) : CommandElabM (TSyntax `term) := do
  if packed then
    let payload ← Slices.packByteValues values
    return ← `(ArrayCode.packedBytes $(quote values.size) $(quote payload))
  if let some first := values[0]? then
    if values.all (· == first) then
      return ← `(ArrayCode.constant $(quote values.size) $(quote first))
    if (values.mapIdx fun index value => value == index).all id then
      return ← `(ArrayCode.range $(quote values.size))
    if (values.mapIdx fun index value => value == first + index).all id then
      return ← `(ArrayCode.linear $(quote values.size) $(quote first))
    if (values.mapIdx fun index value => value == (first + index) % values.size).all id then
      return ← `(ArrayCode.rotate $(quote values.size) $(quote first))
    let run := (values.toList.takeWhile (· == first)).length
    if 1 < run && run < values.size then
      let some next := values[run]? | throwError "source run is absent"
      if first ≤ next then
        let step := next - first
        if (values.mapIdx fun index value => value == first + step * (index / run)).all id then
          return ← `(ArrayCode.linearRuns $(quote values.size) $(quote first) $(quote step) $(quote run))
    if 1 < run && run < values.size && values.size % run == 0 then
      let compact := (Array.range (values.size / run)).map fun index => (values[index * run]?).getD 0
      if (values.mapIdx fun index value => value == (compact[index / run]?).getD 0).all id then
        let encoded ← literalCode compact
        return ← `(ArrayCode.lookupRuns $(quote values.size) $(quote run) $encoded)
  literalCode values

private def integerCode (value : Int) : CommandElabM (TSyntax `term) :=
  if value ≥ 0 then `(Int.ofNat $(quote value.toNat))
  else `(Int.negSucc $(quote (-value - 1).toNat))

private def blockCode (block : Block) (packed : Bool) : CommandElabM (TSyntax `term) := do
  match block with
  | .affine length first stride =>
    `(BlockCode.affine $(quote length) $(quote first) $(← integerCode stride))
  | .dense values => `(BlockCode.dense $(← arrayCode values packed))
  | .periodic count stride values =>
    `(BlockCode.periodic $(quote count) $(← integerCode stride) $(← arrayCode values packed))

private def sliceBlock (block : Block) (start count : Nat) : Array Block := Id.run do
  if start = 0 ∧ count = block.length then return #[block]
  match block with
  | .affine _ _ step => return #[.affine count ((block.get? start).getD 0) step]
  | .dense values => return #[.dense (values.extract start (start + count))]
  | .periodic _ stride values =>
    let leading := min count ((values.size - start % values.size) % values.size)
    let cycleCount := (count - leading) / values.size
    let trailing := (count - leading) % values.size
    let mut result := #[]
    if leading > 0 then
      result := result.push (.dense ((Array.range leading).map fun i =>
        (block.get? (start + i)).getD 0))
    if cycleCount > 0 then
      result := result.push (.periodic cycleCount stride
        ((Array.range values.size).map fun i => (block.get? (start + leading + i)).getD 0))
    if trailing > 0 then
      result := result.push (.dense ((Array.range trailing).map fun i =>
        (block.get? (start + leading + cycleCount * values.size + i)).getD 0))
    return result
private def sliceColumn (column : Column) (start count : Nat) : Column := Id.run do
  let mut position := 0
  let mut blocks := #[]
  for block in column.blocks do
    let first := max start position
    let last := min (start + count) (position + block.length)
    if first < last then blocks := blocks ++ sliceBlock block (first - position) (last - first)
    position := position + block.length
  return ⟨blocks⟩

private def artifact (path : TSyntax `str) : CommandElabM Artifact := do
  let source ← IO.FS.readFile path.getString
  match parse source with
  | .ok value => pure value
  | .error error => throwError "setup code import failed: {error}"

private partial def appendData (parts : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  if parts.isEmpty then return ← `(([] : List BlockCode))
  if parts.size == 1 then return parts[0]!
  let left ← appendData (parts.extract 0 (parts.size / 2))
  let right ← appendData (parts.extract (parts.size / 2) parts.size)
  `(List.append $left $right)

private def emit (name : TSyntax `ident) (blocks : Array (TSyntax `term)) : CommandElabM Unit := do
  if blocks.size ≤ 128 then
    withEnableInfoTree false <| elabCommand (← `(def $name : List BlockCode := [$[$blocks],*]))
  else
    let mut parts := #[]
    for index in [:(blocks.size + 127) / 128] do
      let part := mkIdent (name.getId.appendAfter s!"Data{index}")
      let values := blocks.extract (index * 128) (min blocks.size ((index + 1) * 128))
      withEnableInfoTree false <| elabCommand (← `(def $part : List BlockCode := [$[$values],*]))
      parts := parts.push (← `($part))
    let value ← appendData parts
    withEnableInfoTree false <| elabCommand (← `(def $name : List BlockCode := $value))

private def emitSpan (source : Artifact) (name : TSyntax `ident)
    (physical first count id : Nat) : CommandElabM Unit := do
  let some column := source.columns[physical]? | throwError "source column is absent"
  let some region := source.tables.find? (fun region => region.id == id)
    | throwError "packed source region is absent"
  unless first + count ≤ column.blocks.size do throwError "source block span is out of bounds"
  let mut position := 0
  let mut blocks := #[]
  for (block, index) in column.blocks.toList.zipIdx do
    let finish := position + block.length
    if first ≤ index && index < first + count then
      let packed := region.offset ≤ position && finish ≤ region.offset + region.length
      blocks := blocks.push (← blockCode block packed)
    position := finish
  emit name blocks

private def emitRegion (source : Artifact) (name : TSyntax `ident)
    (id physical first count packed : Nat) : CommandElabM Unit := do
  let some column := source.columns[physical]? | throwError "source column is absent"
  let some region := source.tables.find? (fun region => region.id == id)
    | throwError "source region is absent"
  unless packed ≤ 1 do throwError "invalid packed source mode"
  let sliced := sliceColumn column region.offset region.length
  unless Slices.matchesSource column sliced region.offset region.length do
    throwError "source slice changed a value"
  unless first + count ≤ sliced.blocks.size do throwError "source block span is out of bounds"
  let blocks ← (sliced.blocks.extract first (first + count)).mapM
    (fun block => blockCode block (packed == 1))
  emit name blocks

declare_syntax_cat setup_code_spec
syntax ident " := " "column " num " block_start " num " block_count " num
  " packed_region " num : setup_code_spec
syntax ident " := " "region " num " column " num " block_start " num " block_count " num
  " packed_bytes " num : setup_code_spec

/-- Parse the source once for a complete capture. Each request emits data only.
The separate kernel bindings check its exact relation to the imported columns. -/
elab "import_setup_code_capture " "from " path:str " [" specs:setup_code_spec,* "]" : command => do
  let source ← artifact path
  for spec in specs.getElems do
    match spec with
    | `(setup_code_spec| $name:ident := column $physical:num block_start $first:num
        block_count $count:num packed_region $id:num) =>
      emitSpan source name physical.getNat first.getNat count.getNat id.getNat
    | `(setup_code_spec| $name:ident := region $id:num column $physical:num
        block_start $first:num block_count $count:num packed_bytes $packed:num) =>
      emitRegion source name id.getNat physical.getNat first.getNat count.getNat packed.getNat
    | _ => throwError "unknown setup code request"

/-- Supply a conversion proof. The kernel checks the complete claimed type;
this command does not ask the elaborator to unfold literal arrays. -/
elab "setup_code_binding " name:ident " : " statement:term : command => do
  let type ← liftTermElabM do
    let value ← Term.elabType statement
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  unless type.isAppOfArity ``Eq 3 do throwError "setup binding requires an equality"
  let left := type.getAppArgs[1]!
  let proof ← liftTermElabM <| Meta.mkEqRefl left
  let fullName := (← getCurrNamespace) ++ name.getId
  liftCoreM <| addDecl (.thmDecl {name := fullName, levelParams := [], type, value := proof})

end Airbender.Compiler.PackedSetupImport
