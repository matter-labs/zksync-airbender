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
def State0 : State := { pc := 0, regFile := fun _ => 0, mem := fun _ => 0 }

theorem symRun_append_eq {a b : List Instr} {σ σ1 σ2 : SState} (h1 : symRun a σ = some σ1)
    (h2 : symRun b σ1 = some σ2) : symRun (a ++ b) σ = some σ2 := by
  induction a generalizing σ with
  | nil => simp only [symRun, Option.some.injEq] at h1; subst h1; exact h2
  | cons i is ih =>
    simp only [symRun] at h1 ⊢
    obtain ⟨τ, h, hτ⟩ := Option.bind_eq_some_iff.mp h1
    simp only [List.cons_append, symRun, h, Option.bind_some]; exact ih hτ

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

/-- Chunk size of the kernel runs: each chunk starts from a literal state, so the kernel's cost stays linear in the
block length (one run over a long block re-walks the lazily built state: quadratic). -/
def chunkLen : Nat := 64

/-- Runs the executor on `words` (decoded) and adds `X.instrs`, `X.σ`, `X.dec`, `X.run`, `X.wf`; the run is checked
chunk by chunk (`X.c<k>`, `X.s<k>`, `X.run<k>`). -/
def symDefs (x : TSyntax `ident) (words : Term) : CommandElabM Unit := do
  let n := x.getId
  let ws ← liftTermElabM do
    let ty := mkApp (Lean.mkConst ``List [0]) (mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``RV.Instr))
    unsafe evalTerm (List (Option Instr)) ty (← `(($words).map RV.decode))
  let instrs := ws.filterMap id
  unless instrs.length == ws.length do throwError "sym: a word does not decode"
  let full := (← getCurrNamespace) ++ n
  let listI := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``RV.Instr)
  let stT := Lean.mkConst ``RV.Sym.SState
  -- chunks and the states between them
  let chunks := (List.range ((instrs.length + chunkLen - 1) / chunkLen)).map fun k =>
    (instrs.drop (k * chunkLen)).take chunkLen
  let mut σ := initState
  let mut k := 0
  let mut prev : Expr := Lean.mkConst ``RV.Sym.initState
  let mut runs : Array Expr := #[]
  for c in chunks do
    k := k + 1
    let some σ' := symRun c σ | throwError "sym: the symbolic run fails (chunk {k})"
    let cn := full ++ Name.mkSimple s!"c{k}"; let sn := full ++ Name.mkSimple s!"s{k}"
    let rn := full ++ Name.mkSimple s!"run{k}"
    -- the new state as a delta over the previous one (new nodes, writes, conditions in front of the old lists), so
    -- that the kernel's check `Eq.refl` meets the old state's lists by name and stops there
    let dn := σ'.pool.nodes.length - σ.pool.nodes.length
    let dw := σ'.writes.length - σ.writes.length
    let dc := σ'.conds.length - σ.conds.length
    let delta := σ'.pool.nodes.drop dn == σ.pool.nodes && σ'.writes.drop dw == σ.writes && σ'.conds.drop dc == σ.conds
    let stE ← liftTermElabM do
      if !delta || k == 1 then pure (toExpr σ') else
      let app := fun (_ : Expr) (l : Expr) (r : Expr) => mkAppM ``HAppend.hAppend #[l, r]
      let pv := mkApp (Lean.mkConst ``RV.Sym.SState.pool) prev
      let nodes ← app (Lean.mkConst ``RV.Sym.Node) (toExpr (σ'.pool.nodes.take dn))
        (mkApp (Lean.mkConst ``RV.Sym.Pool.nodes) pv)
      let keys ← app (Lean.mkConst ``Nat) (toExpr (σ'.pool.keys.take dn)) (mkApp (Lean.mkConst ``RV.Sym.Pool.keys) pv)
      let writes ← app (Lean.mkConst ``RV.Sym.SWrite) (toExpr (σ'.writes.take dw))
        (mkApp (Lean.mkConst ``RV.Sym.SState.writes) prev)
      let conds ← app (Lean.mkConst ``RV.Sym.SCond) (toExpr (σ'.conds.take dc))
        (mkApp (Lean.mkConst ``RV.Sym.SState.conds) prev)
      pure (mkApp4 (Lean.mkConst ``RV.Sym.SState.mk)
        (mkApp3 (Lean.mkConst ``RV.Sym.Pool.mk) nodes keys (toExpr σ'.pool.len)) (toExpr σ'.regs) writes conds)
    liftCoreM do
      addDef cn listI (toExpr c)
      addDef sn stT stE
    let ty := ← liftTermElabM do
      mkEq (mkApp2 (Lean.mkConst ``RV.Sym.symRun) (Lean.mkConst cn) prev) (← mkAppM ``Option.some #[Lean.mkConst sn])
    let pf ← liftTermElabM do mkEqRefl (← mkAppM ``Option.some #[Lean.mkConst sn])
    liftCoreM do addDecl (.thmDecl { name := rn, levelParams := [], type := ty, value := pf })
    runs := runs.push (Lean.mkConst rn)
    prev := Lean.mkConst sn
    σ := σ'
  -- the whole block: `X.instrs = c1 ++ (c2 ++ …)`, `X.σ = s<n>`, and its run by `symRun_append_eq`
  let cs := (List.range k).map fun j => Lean.mkConst (full ++ Name.mkSimple s!"c{j + 1}")
  let instrsE ← liftTermElabM do
    match cs.reverse with
    | [] => pure (toExpr ([] : List Instr))
    | l :: rest => rest.foldlM (fun acc c => mkAppM ``HAppend.hAppend #[c, acc]) l
  liftCoreM do
    addDef (full ++ `instrs) listI instrsE
    addDef (full ++ `σ) stT (toExpr σ)  -- flat: lookups in later proofs do not walk the chunks' appends
  let runPf ← liftTermElabM do
    match runs.toList.reverse with
    | [] => mkAppM ``rfl #[← mkAppM ``Option.some #[Lean.mkConst ``RV.Sym.initState]]
    | r :: rest => rest.foldlM (fun acc h => mkAppM ``RV.Sym.symRun_append_eq #[h, acc]) r
  let runTy ← liftTermElabM do
    mkEq (mkApp2 (Lean.mkConst ``RV.Sym.symRun) (Lean.mkConst (full ++ `instrs)) (Lean.mkConst ``RV.Sym.initState))
      (← mkAppM ``Option.some #[Lean.mkConst (full ++ `σ)])
  liftCoreM do addDecl (.thmDecl { name := full ++ `run, levelParams := [], type := runTy, value := runPf })
  let iI := mkIdent (n ++ `instrs); let iσ := mkIdent (n ++ `σ)
  elabCommand (← `(theorem $(mkIdent (n ++ `dec)) : (($words).map RV.decode) = ($iI).map some := by
    decide +kernel))
  elabCommand (← `(theorem $(mkIdent (n ++ `wf)) : ($iσ).pool.WF := RV.Sym.wf_of_run _ _ $(mkIdent (n ++ `run))))
  logInfo m!"{n}: {instrs.length} instructions in {k} chunks, {σ.pool.len} nodes, {σ.writes.length} writes, {σ.conds.length} conditions"

/-- A leaf function: `code` is a straight-line body and `ret`. -/
elab "sym_block " x:ident " := " code:term : command => do
  symDefs x (← `(($code).dropLast))
  elabCommand (← `(theorem $(mkIdent (x.getId ++ `ret)) : $code = ($code).dropLast ++ [RV.Sym.retWord] := by
    decide +kernel))

/-- A straight-line block (no `ret`). -/
elab "sym_run " x:ident " := " words:term : command => symDefs x words

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

/-- Replaces every `Pool.val c p i` in the goal by a fresh variable (after `sym_unfold`: the cut values become
atoms, so that `simp` does not look into the pool). -/
elab "sym_generalize" : tactic => Tactic.withMainContext do
  let g ← Tactic.getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let mut seen : Array Expr := #[]
  for t in collectVals tgt #[] do
    unless seen.contains t do seen := seen.push t
  -- also open terms (`Pool.val c p i` with `c` a variable): `collectVals` keeps those with closed `p`, `i`
  let args := seen.map fun e => { expr := e : GeneralizeArg }
  let (_, g') ← g.generalize args
  Tactic.replaceMainGoal [g']

theorem getReg_x0 (S : State) : S.getReg (BitVec.ofNat 5 0) = 0#32 := rfl

/-- The side goals of `returnsW_of_sym` about regions (`hR`, `hA`, `hdst`): unfolded to linear arithmetic over the
initial registers, for `omega` with the caller's hypotheses. -/
macro "sym_side" : tactic => `(tactic| (
  simp (disch := decide) only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    forall_const, and_true, RV.Sym.Region.Holds, RV.Sym.Apart, RV.Sym.initPool_val, RV.Sym.getReg_x0,
    BitVec.toNat_ofNat, Nat.zero_mod, RV.ROM_END, RV.RAM_END]
  all_goals omega))

end RV.Sym
