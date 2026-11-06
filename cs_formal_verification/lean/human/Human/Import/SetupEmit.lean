import Human.Import.SetupBlocks
import Lean

/- `import_setup_blocks name from "path"` reads a native setup JSON at elaboration time and
   adds `name : Airbender.Import.Setup.SetupData` with one declaration per column. The terms
   are built directly as kernel expressions (no surface syntax), so elaboration cost stays
   linear in the number of blocks. Lake tracks the file through the `needs` input of the
   library containing the use. -/

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

private def blockE : Block → Expr
  | .affine n f s => mkAppN (mkConst ``Airbender.Import.Setup.Block.affine) #[natE n, intE f, intE s]
  | .dense vs => mkApp (mkConst ``Airbender.Import.Setup.Block.dense)
      (arrayE intTy (vs.toList.map intE))
  | .periodic r s vs => mkAppN (mkConst ``Airbender.Import.Setup.Block.periodic)
      #[natE r, intE s, arrayE intTy (vs.toList.map intE)]

private def blocksE (bs : List Block) : Expr := listE blockTy (bs.map blockE)

private def blocksTy : Expr := mkApp (mkConst ``List [Level.zero]) blockTy

private def tableE (t : Table) : Expr :=
  mkAppN (mkConst ``Airbender.Import.Setup.Table.mk)
    #[natE t.id, natE t.offset, natE t.length, natE t.width, natE t.keyColumns]

/-- Kernel-checked definition without code generation: the data is used by kernel reduction. -/
private def addDef (name : Name) (ty value : Expr) : CoreM Unit :=
  addDecl <| .defnDecl {
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
        addDef n blocksTy (blocksE d.columns[i])
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
