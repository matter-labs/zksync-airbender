module
public import Human.Import.SetupBlocks
public meta import Human.Import.SetupBlocks
public import Human.Import.Exec.Decode
public meta import Human.Import.Exec.Decode
public import Lean
public meta import Lean

public meta section

/- TRUSTED: review. Not kernel-checked: the decoding of the setup JSON (`parseSetup`: the JSON value from
   `Json.parse`, read field by field).

   `import_setup_blocks name from "path"` reads a native setup JSON at elaboration time and
   adds `name : Airbender.Import.Setup.SetupData`: the trace length, every generic column and the two virtual range
   columns, each as the JSON blocks themselves (`affine`, `dense`, `periodic`), with one declaration per column, a
   named suffix every 128 blocks (`addColumn`) and small shared literal tails. The terms are built directly as kernel expressions (no surface syntax), so
   elaboration cost stays linear in the number of blocks. Lake tracks the file through the `needs` input of the
   library containing the use. Kernel proofs give the meaning of the rows. -/

namespace Airbender.Import.Setup

open Lean Elab Command

private def natE (n : Nat) : Lean.Expr := mkRawNatLit n

private def intE (i : Int) : Lean.Expr :=
  if i < 0 then mkApp (mkConst ``Int.negSucc) (natE (-i - 1).toNat)
  else mkApp (mkConst ``Int.ofNat) (natE i.toNat)

private def listE (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

private def arrayE (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``Array.mk [Level.zero]) ty (listE ty xs)

private def intTy : Lean.Expr := mkConst ``Int
private def blockTy : Lean.Expr := mkConst ``Airbender.Import.Setup.Block

private def blockE : Block → Lean.Expr
  | .affine n f s => mkAppN (mkConst ``Airbender.Import.Setup.Block.affine) #[natE n, intE f, intE s]
  | .dense vs => mkApp (mkConst ``Airbender.Import.Setup.Block.dense)
      (arrayE intTy (vs.toList.map intE))
  | .periodic r s vs => mkAppN (mkConst ``Airbender.Import.Setup.Block.periodic)
      #[natE r, intE s, arrayE intTy (vs.toList.map intE)]

private def blocksE (bs : List Block) : Lean.Expr := listE blockTy (bs.map blockE)

section Parse

/-- Member `k` of a JSON object, decoded. -/
def get [Decode α] (j : Airbender.Json.Value) (k : String) : Except String α := do
  let .obj ms := j | throw s!"expected an object with field {k}"
  let some v := ms.lookup k | throw s!"missing field {k}"
  Decode.decode v

instance : Decode Int := ⟨fun | .int n => .ok n | _ => .error "expected an integer"⟩
instance : Decode Airbender.Json.Value := ⟨.ok⟩

def blockOf (j : Airbender.Json.Value) : Except String Block := do
  match ← (get j "kind" : Except String String) with
  | "affine" => return .affine (← get j "length") (← get j "first") (← get j "step")
  | "dense" => return .dense (← get j "values")
  | "periodic" => return .periodic (← get j "repetitions") (← get j "stride") (← get j "values")
  | k => throw s!"unknown block kind {k}"

def blocksOf (j : Airbender.Json.Value) : Except String (List Block) := do
  (← (get j "blocks" : Except String (List Airbender.Json.Value))).mapM blockOf

/-- Parse the setup JSON text (`Json.parse`, fixed by `ParseSoundClaim` and `TextUniqueClaim`). -/
def parseSetup (text : String) : Except String SetupData := do
  let j ← Airbender.Json.parse text.toUTF8
  let version : Nat ← get j "version"
  if version != 1 then throw s!"unsupported setup version {version}"
  let columns : List Airbender.Json.Value ← get j "columns"
  return { traceLen := ← get j "trace_len", columns := (← columns.mapM blocksOf).toArray,
           range16 := ← blocksOf (← get j "range16"), timestampRange := ← blocksOf (← get j "timestamp_range") }

end Parse

private def blocksTy : Lean.Expr := mkApp (mkConst ``List [Level.zero]) blockTy

/-- Kernel-checked data definition without code generation. -/
private def addDataDef (name : Name) (ty value : Lean.Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl {
    name, levelParams := [], type := ty, value, hints := .abbrev, safety := .safe }

/-- Share long literal lists through small definitions. Their values stay definitionally equal. -/
private partial def shareDataLists (base : Name) (value : Lean.Expr) : StateT Nat CoreM Lean.Expr := do
  if value.isAppOfArity ``List.cons 3 then
    let ty := value.getAppArgs[0]!
    let mut entries : Array Lean.Expr := #[]
    let mut rest := value
    while rest.isAppOfArity ``List.cons 3 do
      let args := rest.getAppArgs
      entries := entries.push (← shareDataLists base args[1]!)
      rest := args[2]!
    let mut tail ← shareDataLists base rest
    let mut stop := entries.size
    while stop > 0 do
      let first := stop - 128
      let mut chunk := tail
      for index in (List.range (stop - first)).reverse do
        chunk := mkApp3 (mkConst ``List.cons [Level.zero]) ty entries[first + index]! chunk
      if entries.size > 128 then
        let index ← getThe Nat
        set (index + 1)
        let name := base.appendAfter s!"_data{index}"
        liftM <| addDataDef name (mkApp (mkConst ``List [Level.zero]) ty) chunk
        tail := mkConst name
      else
        tail := chunk
      stop := first
    return tail
  match value with
  | .app f a => return mkApp (← shareDataLists base f) (← shareDataLists base a)
  | _ => return value

/-- Expose the imported data with bounded declaration depth and the same kernel value. -/
private def addDef (name : Name) (ty value : Lean.Expr) : CoreM Unit := do
  let (value, _) ← (shareDataLists name value).run 0
  addDataDef name ty value

/-- A column as suffix definitions: `name_from{s}`, for each multiple `s` of 128 below the block count, holds the
    blocks from block `s` on: the next 128 blocks, then `name_from{s + 128}`. `name` is `name_from0`. The value of
    `name` is the list of the blocks, as `addDef` gives it; the scans start from a named suffix. -/
private def addColumn (name : Name) (blocks : List Block) : CoreM Unit := do
  let blocks := blocks.toArray
  let mut tail := mkApp (mkConst ``List.nil [Level.zero]) blockTy
  let mut shared := 0
  for chunk in (List.range ((blocks.size + 127) / 128)).reverse do
    let start := 128 * chunk
    let mut value := tail
    for index in (List.range (min 128 (blocks.size - start))).reverse do
      let (block, next) ← (shareDataLists name (blockE blocks[start + index]!)).run shared
      shared := next
      value := mkApp3 (mkConst ``List.cons [Level.zero]) blockTy block value
    let suffix := name.appendAfter s!"_from{start}"
    addDataDef suffix blocksTy value
    tail := mkConst suffix
  addDataDef name blocksTy tail

syntax (name := importSetupBlocks) "import_setup_blocks " ident " from " str : command

@[command_elab importSetupBlocks]
def elabImportSetupBlocks : CommandElab := fun stx => do
  let name : Ident := ⟨stx[1]⟩
  let some path := stx[3].isStrLit? | throwUnsupportedSyntax
  let text ← IO.FS.readFile path
  let d ← match parseSetup text with
    | .ok d => pure d
    | .error e => throwError "setup import failed: {e}"
  let base := (← getCurrNamespace) ++ name.getId
  liftCoreM do
    let mut colNames : Array Name := #[]
    for h : i in [0:d.columns.size] do
      let n := base.appendAfter s!"_col{i}"
      addColumn n d.columns[i]
      colNames := colNames.push n
    let range16 := base.appendAfter "_range16"
    addDef range16 blocksTy (blocksE d.range16)
    let timestampRange := base.appendAfter "_timestampRange"
    addDef timestampRange blocksTy (blocksE d.timestampRange)
    let cols := arrayE blocksTy (colNames.toList.map fun n => mkConst n)
    let value := mkAppN (mkConst ``Airbender.Import.Setup.SetupData.mk)
      #[natE d.traceLen, cols, mkConst range16, mkConst timestampRange]
    addDef base (mkConst ``Airbender.Import.Setup.SetupData) value

end Airbender.Import.Setup
