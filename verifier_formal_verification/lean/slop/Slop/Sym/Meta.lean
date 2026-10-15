import Slop.Sym.Func

/-! # Tooling: running the executor while elaborating

* `sym_block X := code` runs the symbolic executor on `code` minus its final `ret` and adds
  `X.instrs`, `X.σ` (the final symbolic state, as a literal), `X.dec`, `X.ret`, `X.run : symRun X.instrs initState =
  some X.σ` (one kernel evaluation) and `X.wf`. Later facts about `X.σ` are decided on the literal.
* `sym_unfold [cuts] using l depth d` replaces each `Pool.val c X.σ.pool e` in the goal (closed `e`, not a cut) by the term it denotes
  (`toTree_eval`), stopping at the ids `cuts`. -/

namespace RV.Sym
open Lean Elab Command Term Meta

deriving instance DecidableEq for RV.Cond
deriving instance DecidableEq for RV.Instr
deriving instance DecidableEq for RV.Sym.Node
deriving instance DecidableEq for RV.Sym.Pool
deriving instance DecidableEq for RV.Sym.SState
deriving instance ToExpr for RV.Op
deriving instance ToExpr for RV.FieldOp
deriving instance ToExpr for RV.Cond
deriving instance ToExpr for RV.Instr
deriving instance ToExpr for RV.Sym.Node
deriving instance ToExpr for RV.Sym.Pool
deriving instance ToExpr for RV.Sym.SReg
deriving instance ToExpr for RV.Sym.SWrite
deriving instance ToExpr for RV.Sym.SCond
deriving instance ToExpr for RV.Sym.SState
deriving instance ToExpr for RV.Sym.Tree

/-- Some state, for facts that hold in every context. -/
def State0 : State := ⟨0, fun _ => 0, fun _ => 0⟩

theorem wf_of_run (instrs : List Instr) (σ : SState) (h : symRun instrs initState = some σ) : σ.pool.WF :=
  (symRun_mono (ctxOf State0) instrs State0 initState σ (rel_init State0) condsOK_init h).2.1.1

/-- A loaded word, read back: node `i` loads 4 bytes at register `b` (initial value) plus `k`. -/
theorem load_val (instrs : List Instr) (σ : SState) (hrun : symRun instrs initState = some σ) (S : State)
    (i b : Nat) (k : Word) (sg : Bool) (hb : b < 32) (hi : i < σ.pool.len) (h : nodeAt σ.pool i = .load 4 sg b k) :
    σ.pool.val (ctxOf S) i = read S.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 := by
  obtain ⟨-, he, -⟩ := symRun_mono (ctxOf S) instrs S initState σ (rel_init S) condsOK_init hrun
  rw [(nodeAt_spec (ctxOf S) _ he.1 i hi).2, h]
  simp only [Node.eval]
  rw [val_var S σ.pool he b hb]
  cases sg <;> simp [ctxOf, sext_word]

private def addDef (n : Name) (type val : Expr) : CoreM Unit := do
  addAndCompile <| .defnDecl (mkDefinitionValEx n [] type val (.regular 0) .safe [])

elab "sym_block " x:ident " := " code:term : command => do
  let n := x.getId
  let ws ← liftTermElabM do
    let ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``Option [0]) (mkConst ``RV.Instr))
    unsafe evalTerm (List (Option Instr)) ty (← `(($code).dropLast.map RV.decode))
  let instrs := ws.filterMap id
  unless instrs.length == ws.length do throwError "sym_block: a word does not decode"
  let some σ := symRun instrs initState | throwError "sym_block: the symbolic run fails"
  let full := (← getCurrNamespace) ++ n
  liftCoreM do
    addDef (full ++ `instrs) (mkApp (mkConst ``List [0]) (mkConst ``RV.Instr)) (toExpr instrs)
    addDef (full ++ `σ) (mkConst ``RV.Sym.SState) (toExpr σ)
  let iI := mkIdent (n ++ `instrs); let iσ := mkIdent (n ++ `σ)
  elabCommand (← `(theorem $(mkIdent (n ++ `dec)) : (($code).dropLast.map RV.decode) = ($iI).map some := by
    decide +kernel))
  elabCommand (← `(theorem $(mkIdent (n ++ `ret)) : $code = ($code).dropLast ++ [RV.Sym.retWord] := by
    decide +kernel))
  elabCommand (← `(theorem $(mkIdent (n ++ `run)) : RV.Sym.symRun $iI RV.Sym.initState = some $iσ := by
    decide +kernel))
  elabCommand (← `(theorem $(mkIdent (n ++ `wf)) : ($iσ).pool.WF := RV.Sym.wf_of_run _ _ $(mkIdent (n ++ `run))))
  logInfo m!"{n}: {instrs.length} instructions, {σ.pool.len} nodes, {σ.writes.length} writes, {σ.conds.length} conditions"

/-- The subterms `Pool.val c p e` with `p` and `e` closed. -/
partial def collectVals (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``RV.Sym.Pool.val 3 then
    let as := e.getAppArgs
    if !as[1]!.hasFVar && !as[1]!.hasMVar && !as[2]!.hasFVar && !as[2]!.hasMVar then acc.push e
    else as.foldl (fun acc a => collectVals a acc) acc
  else match e with
    | .app f a => collectVals a (collectVals f acc)
    | .lam _ t b _ | .forallE _ t b _ => collectVals b (collectVals t acc)
    | .letE _ t v b _ => collectVals b (collectVals v (collectVals t acc))
    | .mdata _ b | .proj _ _ b => collectVals b acc
    | _ => acc

syntax "sym_unfold" (" [" num,* "]")? (" using " term)? (" depth " num)? : tactic

elab_rules : tactic
  | `(tactic| sym_unfold $[[$cs,*]]? $[using $t]? $[depth $d]?) => Tactic.withMainContext do
  let mut cut : List Nat := (cs.map fun cs => cs.getElems.toList.map (·.getNat)).getD []
  if let some t := t then
    cut := cut ++ (← unsafe Term.evalTerm (List Nat) (mkApp (mkConst ``List [0]) (mkConst ``Nat)) t)
  let dep := (d.map (·.getNat)).getD 64
  let g ← Tactic.getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let mut seen : Array Expr := #[]
  let mut eqs : Array Expr := #[]
  let found := collectVals tgt #[]
  for t in found do
    if seen.contains t then continue
    seen := seen.push t
    let as := t.getAppArgs
    let (c, p, e) := (as[0]!, as[1]!, as[2]!)
    -- `p` is `X.σ.pool`: its well-formedness is `X.wf`
    let some σn := (if p.isAppOfArity ``RV.Sym.SState.pool 1 then p.appArg!.constName? else none)
      | throwError "sym_unfold: expected `X.σ.pool`, got {p}"
    let wf := Lean.mkConst (σn.getPrefix ++ `wf)
    let i ← unsafe evalExpr Nat (mkConst ``Nat) e
    if cut.contains i then continue
    let pv ← unsafe evalExpr Pool (mkConst ``RV.Sym.Pool) p
    let cut' := cut.filter (· != i)
    let T := toTree pv cut' dep i
    let cutE := toExpr cut'
    let hi ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``RV.Sym.Pool.len #[p]])
    let pf ← mkAppM ``RV.Sym.toTree_eval #[c, p, wf, cutE, mkNatLit dep, mkNatLit i, hi]
    let pf ← mkEqSymm pf
    let ty ← mkEq t (← mkAppM ``RV.Sym.Tree.eval #[c, ← mkAppM ``RV.Sym.Pool.val #[c, p], toExpr T])
    eqs := eqs.push (← mkExpectedTypeHint pf ty)
  let mut g := g
  for h in eqs do
    let r ← g.rewrite (← g.getType) h
    g ← g.replaceTargetEq r.eNew r.eqProof
  Tactic.replaceMainGoal [g]
  Tactic.evalTactic (← `(tactic| simp only [RV.Sym.Tree.eval]))

/-- The side goals of `returnsW_of_sym` about regions (`hR`, `hA`, `hdst`): unfolded to linear arithmetic over the
initial registers, for `omega` with the caller's hypotheses. -/
macro "sym_side" : tactic => `(tactic| (
  simp (disch := decide) only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    forall_const, and_true, RV.Sym.Region.Holds, RV.Sym.Apart, RV.Sym.initPool_val, RV.ROM_END, RV.RAM_END]
  all_goals omega))

end RV.Sym
