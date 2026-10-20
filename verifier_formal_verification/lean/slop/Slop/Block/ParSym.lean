import Slop.Sym.Meta

/-! # Parallel symbolic blocks

A long straight-line block is split into parts of `P` instructions, one module per part, so that lake checks the
parts' kernel runs in parallel:
* `sym_states X P := code` (module before the parts): `X.st<j>`, the symbolic state after `j` parts (interpreted,
  flat literals; the kernel only type checks them).
* `sym_part X P p := code` (module `p`, imports the states): `X.pc<p>` the part's instructions and
  `X.pr<p> : symRun X.pc<p> prev = some X.st<p>`, checked by the kernel (`prev` is `initState` for `p = 1`, else
  `X.st<p-1>`).
* `sym_glue X P := code` (last module): `X.instrs`, `X.σ`, `X.run`, `X.dec`, `X.wf`, `X.ret`, with the statements
  of `sym_block`.
`code` is a block as in `sym_block` (its last word is `ret`). -/

namespace RV.Sym
open Lean Elab Command Term Meta

private def addDefP (n : Name) (type val : Expr) : CoreM Unit := do
  addAndCompile <| .defnDecl (mkDefinitionValEx n [] type val (.regular 0) .safe [])

/-- The decoded instructions of `code` without its `ret`. -/
def straightInstrs (code : Term) : CommandElabM (List Instr) := do
  let ws ← liftTermElabM do
    let ty := mkApp (Lean.mkConst ``List [0]) (mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``RV.Instr))
    unsafe evalTerm (List (Option Instr)) ty (← `((($code).dropLast).map RV.decode))
  let instrs := ws.filterMap id
  unless instrs.length == ws.length do throwError "sym: a word does not decode"
  return instrs

/-- The part `j` (1-based) of `instrs`, `P` instructions each. -/
def partOf (instrs : List Instr) (P j : Nat) : List Instr := ((instrs.drop ((j - 1) * P)).take P)

/-- The number of parts. -/
def nParts (n P : Nat) : Nat := (n + P - 1) / P

elab "sym_states " x:ident P:num " := " code:term : command => do
  let instrs ← straightInstrs code
  let full := (← getCurrNamespace) ++ x.getId
  let P := P.getNat
  let n := nParts instrs.length P
  let mut σ := RV.Sym.initState
  for j in [1:n+1] do
    let some σ' := symRun (partOf instrs P j) σ | throwError "sym: the symbolic run fails (part {j})"
    liftCoreM <| addDefP (full ++ Name.mkSimple s!"st{j}") (Lean.mkConst ``RV.Sym.SState) (toExpr σ')
    σ := σ'
  logInfo m!"{x.getId}: {instrs.length} instructions in {n} parts, {σ.pool.len} nodes at the end"

elab "sym_part " x:ident P:num p:num " := " code:term : command => do
  let instrs ← straightInstrs code
  let full := (← getCurrNamespace) ++ x.getId
  let P := P.getNat
  let j := p.getNat
  let seg := partOf instrs P j
  let prevE : Expr :=
    if j == 1 then Lean.mkConst ``RV.Sym.initState else Lean.mkConst (full ++ Name.mkSimple s!"st{j - 1}")
  let cn := full ++ Name.mkSimple s!"pc{j}"
  let stE := Lean.mkConst (full ++ Name.mkSimple s!"st{j}")
  liftCoreM <| addDefP cn (mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``RV.Instr)) (toExpr seg)
  let ty ← liftTermElabM do
    mkEq (mkApp2 (Lean.mkConst ``RV.Sym.symRun) (Lean.mkConst cn) prevE) (← mkAppM ``Option.some #[stE])
  let pf ← liftTermElabM do mkEqRefl (← mkAppM ``Option.some #[stE])
  liftCoreM do addDecl (.thmDecl { name := full ++ Name.mkSimple s!"pr{j}", levelParams := [], type := ty, value := pf })

elab "sym_glue " x:ident P:num " := " code:term : command => do
  let instrs ← straightInstrs code
  let full := (← getCurrNamespace) ++ x.getId
  let n := nParts instrs.length P.getNat
  let cs := (List.range n).map fun j => Lean.mkConst (full ++ Name.mkSimple s!"pc{j + 1}")
  let listI := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``RV.Instr)
  let stT := Lean.mkConst ``RV.Sym.SState
  let instrsE ← liftTermElabM do
    match cs.reverse with
    | [] => pure (toExpr ([] : List Instr))
    | l :: rest => rest.foldlM (fun acc c => mkAppM ``HAppend.hAppend #[c, acc]) l
  liftCoreM do
    addDefP (full ++ `instrs) listI instrsE
    addDefP (full ++ `σ) stT (Lean.mkConst (full ++ Name.mkSimple s!"st{n}"))
  -- the whole run: `symRun_append_eq` over the parts' runs, right-nested like `instrs`
  let runs := (List.range n).map fun j => Lean.mkConst (full ++ Name.mkSimple s!"pr{j + 1}")
  let runPf ← liftTermElabM do
    match runs.reverse with
    | [] => mkAppM ``rfl #[← mkAppM ``Option.some #[Lean.mkConst ``RV.Sym.initState]]
    | r :: rest => rest.foldlM (fun acc h => mkAppM ``RV.Sym.symRun_append_eq #[h, acc]) r
  let runTy ← liftTermElabM do
    mkEq (mkApp2 (Lean.mkConst ``RV.Sym.symRun) (Lean.mkConst (full ++ `instrs)) (Lean.mkConst ``RV.Sym.initState))
      (← mkAppM ``Option.some #[Lean.mkConst (full ++ `σ)])
  liftCoreM do addDecl (.thmDecl { name := full ++ `run, levelParams := [], type := runTy, value := runPf })
  let iI := mkIdent (x.getId ++ `instrs); let iσ := mkIdent (x.getId ++ `σ)
  elabCommand (← `(theorem $(mkIdent (x.getId ++ `dec)) : (($code).dropLast.map RV.decode) = ($iI).map some := by
    decide +kernel))
  elabCommand (← `(theorem $(mkIdent (x.getId ++ `wf)) : ($iσ).pool.WF := RV.Sym.wf_of_run _ _ $(mkIdent (x.getId ++ `run))))
  elabCommand (← `(theorem $(mkIdent (x.getId ++ `ret)) : $code = ($code).dropLast ++ [RV.Sym.retWord] := by
    decide +kernel))
  logInfo m!"{x.getId}: {instrs.length} instructions in {n} parts"

end RV.Sym
