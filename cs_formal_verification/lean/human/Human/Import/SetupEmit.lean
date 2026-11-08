module
public import Human.Import.SetupBlocks
public meta import Human.Import.SetupBlocks
public import Lean
public meta import Lean

public meta section

/- `import_setup_blocks name from "path"` reads a native setup JSON at elaboration time and
   adds `name : Airbender.Import.Setup.SetupData` with one declaration per column. The terms
   are built directly as kernel expressions (no surface syntax), so elaboration cost stays
   linear in the number of blocks. Lake tracks the file through the `needs` input of the
   library containing the use.

   Structured regions: the JSON blocks of each column are cut at every table edge; for each
   `tables` entry whose id is in `gridCatalogue`, column `c` of the region (`c < width`) is
   emitted as one `grid` block with the catalogue's formula, and rows outside these regions
   keep the (cut) JSON blocks. `checkColumn` then compares every emitted block with the JSON:
   a block identical to the JSON block at the same row, or a cut of an affine JSON block, is
   accepted as is, any other block (grid or cut) row by row against the JSON values; any
   mismatch fails the import. The emitted blocks tile the rows contiguously and the totals
   agree, so the emitted column decodes to the JSON column at every row. This comparison is
   elaborator code (run at import, not by the kernel), trusted like `parseSetup`; the kernel
   never sees the JSON blocks of a grid region. -/

namespace Airbender.Import.Setup

open Lean Elab Command

private def natE (n : Nat) : Expr := mkRawNatLit n

private def intE (i : Int) : Expr :=
  if i < 0 then mkApp (mkConst ``Int.negSucc) (natE (-i - 1).toNat)
  else mkApp (mkConst ``Int.ofNat) (natE i.toNat)

private def listE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

private def arrayE (ty : Expr) (xs : List Expr) : Expr :=
  mkApp2 (mkConst ``Array.mk [Level.zero]) ty (listE ty xs)

private def intTy : Expr := mkConst ``Int
private def blockTy : Expr := mkConst ``Airbender.Import.Setup.Block

private def gridE : GridFn → Expr
  | .digit d w => mkAppN (mkConst ``GridFn.digit) #[natE d, natE w]
  | .xorDigits d₁ d₂ w => mkAppN (mkConst ``GridFn.xorDigits) #[natE d₁, natE d₂, natE w]
  | .xor4x3 => mkConst ``GridFn.xor4x3
  | .rotLow => mkConst ``GridFn.rotLow
  | .rotHigh => mkConst ``GridFn.rotHigh
  | .xor5 => mkConst ``GridFn.xor5
  | .chi k => mkApp (mkConst ``GridFn.chi) (natE k)
  | .xorTable w t => mkAppN (mkConst ``GridFn.xorTable)
      #[natE w, arrayE (mkConst ``Nat) (t.toList.map natE)]

private def blockE : Block → Expr
  | .affine n f s => mkAppN (mkConst ``Airbender.Import.Setup.Block.affine) #[natE n, intE f, intE s]
  | .dense vs => mkApp (mkConst ``Airbender.Import.Setup.Block.dense)
      (arrayE intTy (vs.toList.map intE))
  | .periodic r s vs => mkAppN (mkConst ``Airbender.Import.Setup.Block.periodic)
      #[natE r, intE s, arrayE intTy (vs.toList.map intE)]
  | .grid n f => mkAppN (mkConst ``Airbender.Import.Setup.Block.grid) #[natE n, gridE f]

private def blocksE (bs : List Block) : Expr := listE blockTy (bs.map blockE)

/-! Structured regions -/

/-- Row formulas of the Airbender tables the import recognises (`TableType`,
    cs/src/definitions/table_type.rs; generators in cs/src/tables), one per table column.
    `xorTable` is completed from the data (`fit`). -/
def gridCatalogue : Nat → Option (List GridFn)
  | 4 => some [.digit 256 256, .digit 1 256, .xorDigits 256 1 256]            -- Xor
  | 19 => some [.digit 128 128, .digit 1 128, .xorDigits 128 1 128]          -- Xor7
  | 20 => some [.digit 512 512, .digit 1 512, .xorDigits 512 1 512]          -- Xor9
  | 38 => some [.digit 1 256, .digit 256 256, .xorTable 256 #[]]             -- XorSpecialIota
  | 55 => some [.digit 256 256, .digit 1 256, .digit 65536 3, .xorDigits 256 1 256]  -- Xor8WithCarry
  | 56 => some [.digit 128 128, .digit 1 128, .digit 16384 3, .xorDigits 128 1 128]  -- Xor7WithCarry
  | 57 => some [.digit 1024 16, .digit 128 8, .digit 8 16, .digit 1 8, .xor4x3]      -- Xor4x3
  | 58 => some [.digit 1 256, .digit 256 256, .digit 65536 8, .rotLow, .rotHigh]     -- KeccakXorSplit
  | 64 => some [.digit 1 16, .digit 16 16, .digit 256 16, .digit 4096 16, .digit 65536 16,
      .xor5]                                                                  -- KeccakXor5Nibble
  | 65 => some [.digit 1 16, .digit 16 16, .digit 256 16, .digit 4096 16, .digit 65536 16,
      .chi 0, .chi 1, .chi 2, .chi 3, .chi 4]                                 -- KeccakChi5
  | _ => none

/-- Blocks with their first rows. -/
def placedBlocks (bs : List Block) : Array (Nat × Block) := Id.run do
  let mut out := #[]
  let mut s := 0
  for b in bs do
    out := out.push (s, b)
    s := s + b.len
  return out

/-- The JSON values of rows `[lo, hi)` of a column. -/
def rowsOf (placed : Array (Nat × Block)) (lo hi : Nat) : Array Int := Id.run do
  let mut out : Array Int := Array.mkEmpty (hi - lo)
  for (s, b) in placed do
    let e := s + b.len
    if e ≤ lo then continue
    if hi ≤ s then break
    for i in [max s lo - s : min e hi - s] do
      out := out.push (b.valueAt i)
  return out

/-- Rows `[lo, hi)` of a block (block-relative), as a block. -/
def cut (b : Block) (lo hi : Nat) : Block :=
  match b with
  | .affine _ first step => .affine (hi - lo) (first + step * lo) step
  | b => .dense (((List.range (hi - lo)).map fun j => b.valueAt (lo + j)).toArray)

/-- `xorTable` takes its constants from the data: `t[g]` is the region's row `g * w`
    (where `i % w = 0`); `checkColumn` then checks every row. -/
def fit (placed : Array (Nat × Block)) (first length : Nat) : GridFn → GridFn
  | .xorTable w _ =>
    let rows := rowsOf placed first (first + length)
    .xorTable w (((List.range ((length + w - 1) / w)).map fun g => (rows.getD (g * w) 0).toNat).toArray)
  | f => f

/-- The JSON blocks cut at every row of `edges` that falls strictly inside a block. -/
def cutAt (placed : Array (Nat × Block)) (edges : Array Nat) : Array (Nat × Block) := Id.run do
  let mut out := #[]
  for (s, b) in placed do
    let e := s + b.len
    let inner := (edges.filter fun x => s < x ∧ x < e).qsort (· < ·)
    if inner.isEmpty then
      out := out.push (s, b)
    else
      let mut cur := s
      for x in inner.push e do
        if cur < x then out := out.push (cur, cut b (cur - s) (x - s))
        cur := x
  return out

/-- The emitted column: the grid block of a region at its first row, the (cut) JSON blocks
    outside the regions (`regions`: first row, length, formula). -/
def withGrids (pieces : Array (Nat × Block)) (regions : Array (Nat × Nat × GridFn)) : List Block :=
  pieces.toList.filterMap fun (s, b) =>
    match regions.find? (fun (r, l, _) => r ≤ s ∧ s < r + l) with
    | some (r, l, f) => if s = r then some (.grid l f) else none
    | none => some b

/-- Every emitted block equals the JSON on its rows: identical to the JSON block starting at
    the same row, a cut of the affine JSON block containing it, or equal row by row. Returns
    the first mismatch. -/
def checkColumn (json : Array (Nat × Block)) (emitted : List Block) : Except String Unit := do
  let total := json.foldl (fun t p => t + p.2.len) 0
  let mut k := 0
  for (s, b) in placedBlocks emitted do
    while k + 1 < json.size && json[k + 1]!.1 ≤ s do k := k + 1
    if k < json.size then
      let (s₀, b₀) := json[k]!
      if s₀ == s && b₀ == b then continue
      if let .affine .. := b₀ then
        if s₀ ≤ s && s + b.len ≤ s₀ + b₀.len && cut b₀ (s - s₀) (s - s₀ + b.len) == b then continue
    let rows := rowsOf json s (s + b.len)
    if rows.size != b.len then throw s!"block at row {s} runs past the JSON rows"
    for i in [0:b.len] do
      if rows[i]! != b.valueAt i then
        throw s!"row {s + i}: JSON {rows[i]!}, emitted {b.valueAt i}"
  let emittedTotal := emitted.foldl (fun t b => t + b.len) 0
  if emittedTotal != total then throw s!"emitted {emittedTotal} rows, JSON {total}"

/-- Column `c`: the JSON blocks cut at every table edge, with grid blocks on the recognised
    table regions, checked against the JSON. -/
def structureColumn (tables : Array Table) (c : Nat) (bs : List Block) :
    Except String (List Block) := do
  let json := placedBlocks bs
  let mut regions := #[]
  for t in tables do
    if let some fs := gridCatalogue t.id then
      if fs.length != t.width then throw s!"table {t.id}: width {t.width}, catalogue {fs.length}"
      if h : c < fs.length then
        regions := regions.push (t.offset, t.length, fit json t.offset t.length fs[c])
  let sorted := tables.qsort (fun a b => a.offset < b.offset)
  for i in [1:sorted.size] do
    if sorted[i]!.offset < sorted[i-1]!.offset + sorted[i-1]!.length then
      throw "overlapping table regions"
  let edges := tables.foldl (fun es t => es.push t.offset |>.push (t.offset + t.length)) #[]
  let out := withGrids (cutAt json edges) regions
  match checkColumn json out with
  | .ok () => return out
  | .error e => throw s!"column {c}: {e}"

private def blocksTy : Expr := mkApp (mkConst ``List [Level.zero]) blockTy

private def tableE (t : Table) : Expr :=
  mkAppN (mkConst ``Airbender.Import.Setup.Table.mk)
    #[natE t.id, natE t.offset, natE t.length, natE t.width, natE t.keyColumns]

/-- Kernel-checked definition without code generation: the data is used by kernel reduction, so its body is
    exposed to importing modules (`forceExpose`; no effect in a non-module). -/
private def addDef (name : Name) (ty value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl {
    name, levelParams := [], type := ty, value, hints := .abbrev, safety := .safe }

syntax (name := importSetupBlocks) "import_setup_blocks " ident " from " str : command

@[command_elab importSetupBlocks]
def elabImportSetupBlocks : CommandElab := fun stx => do
  match stx with
  | `(import_setup_blocks $name:ident from $path:str) => do
    let text ← IO.FS.readFile path.getString
    let d ← match parseSetup text with
      | .ok d => pure d
      | .error e => throwError "setup import failed: {e}"
    let base := (← getCurrNamespace) ++ name.getId
    liftCoreM do
      let mut colNames : Array Name := #[]
      for h : i in [0:d.columns.size] do
        let n := base.appendAfter s!"_col{i}"
        let col ← match structureColumn d.tables i d.columns[i] with
          | .ok col => pure col
          | .error e => throwError "setup import failed: {e}"
        addDef n blocksTy (blocksE col)
        colNames := colNames.push n
      let r16 := base.appendAfter "_range16"
      addDef r16 blocksTy (blocksE d.range16)
      let ts := base.appendAfter "_timestampRange"
      addDef ts blocksTy (blocksE d.timestampRange)
      let setupTy := mkConst ``Airbender.Import.Setup.SetupData
      let cols := arrayE blocksTy (colNames.toList.map fun n => mkConst n)
      let tables := arrayE (mkConst ``Airbender.Import.Setup.Table) (d.tables.toList.map tableE)
      let value := mkAppN (mkConst ``Airbender.Import.Setup.SetupData.mk)
        #[natE d.traceLen, cols, mkConst r16, mkConst ts, tables]
      addDef base setupTy value
  | _ => throwUnsupportedSyntax

end Airbender.Import.Setup
