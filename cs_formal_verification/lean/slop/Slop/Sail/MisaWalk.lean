import Slop.Sail.PC

/-!
# Proof search for `MisaOnly` facts about the generated decoder

`MisaOnly action`: successful execution of `action` changes no state, and its result is the same
in every state with the same `misa` image. The leaf lemmas below are the Sail-side facts; the
tactic `misa_walk` builds a proof of `MisaOnly e` for a decoder body `e` by structure.

The builder is proof search, not trusted: it constructs a proof term with `mkAppN` and
`mkLambdaFVars` (no unification of big terms, no metavariables), and the kernel re-checks it
when the enclosing declaration is added. It may use `partial` and metaprogramming; this module
is listed as a tactic module in the trust file. The walk never unfolds a definition: heads are
matched syntactically, `if`/`match` are split by their structure, and every join point
(`have __do_jp := fun …`) is proved once and then used through its hypothesis.
-/

namespace Airbender.Reference.Sail
open Reference.RiscV.Sail _root_.Sail.ArchSem

/-- A property of the existing Sail interpreter: successful execution preserves
    state and can be replayed in any state with the same `misa` image. -/
def MisaOnly {α : Type} (action : SailRV32.SailM α) : Prop :=
  ∀ before value after, run action before = .ok value after →
    after = before ∧ ∀ state, state.regs.get? .misa = before.regs.get? .misa →
      run action state = .ok value state

theorem misa_pure {α : Type} (value : α) : MisaOnly (pure value) := by
  intro before actual after executed
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj executed
  exact ⟨rfl, fun _ _ => rfl⟩

theorem misa_bind {α β : Type} (action : SailRV32.SailM α)
    (next : α → SailRV32.SailM β) (first : MisaOnly action)
    (rest : ∀ value, MisaOnly (next value)) : MisaOnly (action >>= next) := by
  intro before value after executed
  cases initial : run action before with
  | error error middle =>
    rw [run_bind_of_error _ _ _ _ _ initial] at executed
    cases executed
  | ok input middle =>
    obtain ⟨unchanged, replay⟩ := first before input middle initial
    subst middle
    rw [run_bind_of_ok _ _ _ _ _ initial] at executed
    obtain ⟨unchanged, finish⟩ := rest input before value after executed
    subst after
    refine ⟨rfl, fun state same => ?_⟩
    rw [run_bind_of_ok _ _ _ _ _ (replay state same)]
    exact finish state same

theorem misa_read : MisaOnly (SailRV32.readReg .misa) := by
  intro before value after executed
  cases found : before.regs.get? .misa with
  | none =>
    dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects,
      FreeM.liftM, interpretInstructionEffect] at executed
    simp only [found] at executed
    change EStateM.Result.error (_root_.Sail.Error.Unreachable) before =
      EStateM.Result.ok value after at executed
    cases executed
  | some data =>
    have read := read_register found
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (read.symm.trans executed)
    refine ⟨rfl, fun state equal => ?_⟩
    exact read_register equal

theorem misa_ite {α : Type} (condition : Prop) [Decidable condition]
    (yes no : SailRV32.SailM α) (hy : MisaOnly yes) (hn : MisaOnly no) :
    MisaOnly (if condition then yes else no) := by
  by_cases selected : condition <;> simp [selected, hy, hn]

theorem misa_assert (condition : Bool) (message : String) :
    MisaOnly (SailRV32.assert condition message) := by
  cases condition
  · intro before value after executed
    cases executed
  · exact misa_pure ()

theorem misa_throw {α : Type} (error : _root_.Sail.Error SailRV32.exception) :
    MisaOnly (throw error : SailRV32.SailM α) := by
  intro before value after executed
  cases executed

attribute [irreducible] MisaOnly

set_option backward.isDefEq.respectTransparency false in
theorem misa_enabled (extension : SailRV32.extension)
    (supported : extension ∈ [SailRV32.extension.Ext_M, .Ext_Zmmul, .Ext_Zba, .Ext_Zbb, .Ext_B,
      .Ext_Zbkb, .Ext_Zicsr, .Ext_Zimop, .Ext_Sv32, .Ext_Sv39, .Ext_Sv48, .Ext_Sv57]) :
    MisaOnly (SailRV32.Functions.currentlyEnabled extension) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [SailRV32.Functions.currentlyEnabled]
  all_goals
    repeat' first
      | exact misa_read
      | apply misa_pure
      | apply misa_assert
      | apply misa_throw
      | (apply misa_bind <;> try intro)

set_option backward.isDefEq.respectTransparency false in
theorem misa_virtual : MisaOnly (SailRV32.Functions.virtual_memory_supported ()) := by
  unfold SailRV32.Functions.virtual_memory_supported
  repeat' first
    | (apply misa_enabled; simp)
    | apply misa_pure
    | (apply misa_bind <;> try intro)

set_option backward.isDefEq.respectTransparency false in
theorem misa_register (bits : BitVec 5) :
    MisaOnly (SailRV32.Functions.encdec_reg_backwards bits) := by
  unfold SailRV32.Functions.encdec_reg_backwards
  apply misa_pure

set_option backward.isDefEq.respectTransparency false in
theorem misa_opcodes :
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_bop_backwards bits)) ∧
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_iop_backwards bits)) ∧
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_mul_op_backwards bits)) ∧
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_uop_backwards bits)) ∧
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_csrop_backwards bits)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro bits
  all_goals
    simp only [SailRV32.Functions.encdec_bop_backwards, SailRV32.Functions.encdec_iop_backwards,
      SailRV32.Functions.encdec_mul_op_backwards, SailRV32.Functions.encdec_uop_backwards,
      SailRV32.Functions.encdec_csrop_backwards]
    repeat' first
      | apply misa_pure
      | apply misa_assert
      | apply misa_throw
      | (apply misa_bind <;> try intro)
      | apply misa_ite
      | split

theorem misa_bop (bits : BitVec 3) : MisaOnly (SailRV32.Functions.encdec_bop_backwards bits) :=
  misa_opcodes.1 bits

theorem misa_iop (bits : BitVec 3) : MisaOnly (SailRV32.Functions.encdec_iop_backwards bits) :=
  misa_opcodes.2.1 bits

theorem misa_mul (bits : BitVec 3) : MisaOnly (SailRV32.Functions.encdec_mul_op_backwards bits) :=
  misa_opcodes.2.2.1 bits

theorem misa_uop (bits : BitVec 7) : MisaOnly (SailRV32.Functions.encdec_uop_backwards bits) :=
  misa_opcodes.2.2.2.1 bits

theorem misa_csr (bits : BitVec 2) : MisaOnly (SailRV32.Functions.encdec_csrop_backwards bits) :=
  misa_opcodes.2.2.2.2 bits

set_option linter.deprecated false in
/-- A join point `jp` (a `have` whose value is a function) is proven once, as `joined`; its
    uses in `body` are only through the abstract `j` with hypothesis `∀ x, MisaOnly (j x)`. -/
theorem misa_join {α β γ : Type} (jp : α → SailRV32.SailM β)
    (body : (α → SailRV32.SailM β) → SailRV32.SailM γ)
    (joined : ∀ x, MisaOnly (jp x))
    (rest : ∀ j : α → SailRV32.SailM β, (∀ x, MisaOnly (j x)) → MisaOnly (body j)) :
    MisaOnly (letFun jp body) :=
  rest jp joined

namespace Walk

open Lean Meta Elab Tactic

/-- Leaf table: a proof of `MisaOnly (head args)` for the heads that end a branch, or `none`. -/
abbrev Leaves := Name → Array Expr → MetaM (Option Expr)

private def lemmaName (n : Name) : Name := `Airbender.Reference.Sail ++ n

/-- The value type `α` of a `SailM α` type. -/
private def sailArg (t : Expr) : MetaM Expr := do
  let t := t.headBeta
  unless t.isApp do throwError "misaWalk: expected a SailM type, got {t}"
  return t.appArg!

/-- `ext ∈ l` for a literal list `l` (a `cons` spine), found by position; no decidability needed. -/
private partial def listMemProof (ext l : Expr) : MetaM Expr := do
  unless l.isAppOfArity ``List.cons 3 do
    throwError "misaWalk: membership in a non-literal list {l}"
  let α := l.getArg! 0
  let a := l.getArg! 1
  let rest := l.getArg! 2
  if a == ext then return mkAppN (mkConst ``List.Mem.head [Level.zero]) #[α, a, rest]
  return mkAppN (mkConst ``List.Mem.tail [Level.zero]) #[α, ext, a, rest, ← listMemProof ext rest]

/-- The leaves of the generated decoder's `misa`-only clauses and of `pure`/`throw`/`assert`. -/
def decoderLeaves : Leaves := fun name args => do
  let c (n : Name) := mkConst (lemmaName n)
  if name == ``Pure.pure && args.size == 4 then
    return some (mkAppN (c `misa_pure) #[args[2]!, args[3]!])
  if name == `SailRV32.Functions.encdec_reg_backwards && args.size == 1 then
    return some (mkAppN (c `misa_register) #[args[0]!])
  if name == `SailRV32.Functions.encdec_bop_backwards && args.size == 1 then
    return some (mkAppN (c `misa_bop) #[args[0]!])
  if name == `SailRV32.Functions.encdec_iop_backwards && args.size == 1 then
    return some (mkAppN (c `misa_iop) #[args[0]!])
  if name == `SailRV32.Functions.encdec_mul_op_backwards && args.size == 1 then
    return some (mkAppN (c `misa_mul) #[args[0]!])
  if name == `SailRV32.Functions.encdec_uop_backwards && args.size == 1 then
    return some (mkAppN (c `misa_uop) #[args[0]!])
  if name == `SailRV32.Functions.encdec_csrop_backwards && args.size == 1 then
    return some (mkAppN (c `misa_csr) #[args[0]!])
  if name == `SailRV32.Functions.virtual_memory_supported && args.size == 1 then
    return some (c `misa_virtual)
  if name == `SailRV32.Functions.currentlyEnabled && args.size == 1 then
    let lemmaTy ← inferType (mkApp (c `misa_enabled) args[0]!)
    let dom := lemmaTy.bindingDomain!
    let h ← listMemProof dom.appArg! dom.appFn!.appArg!
    return some (mkAppN (c `misa_enabled) #[args[0]!, h])
  if name == `SailRV32.assert && args.size == 2 then
    return some (mkAppN (c `misa_assert) #[args[0]!, args[1]!])
  if name == ``MonadExcept.throw && args.size == 5 then
    return some (mkAppN (c `misa_throw) #[args[3]!, args[4]!])
  return none

mutual

/-- A proof of `MisaOnly e` for a `SailM` term `e`, by structure. Hypotheses `hyps` map the
    join-point variables in scope to their `∀ x, MisaOnly (j x)` proofs. -/
partial def prove (leaves : Leaves) (hyps : List (Expr × Expr)) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if e.isHeadBetaTarget then return ← prove leaves hyps e.headBeta
  if let .letE n t v b _ := e then return ← proveLet leaves hyps e n t v b
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .fvar id =>
    match hyps.find? (fun p => p.1.fvarId! == id) with
    | some (_, hj) => return mkAppN hj args
    | none => throwError "misaWalk: free variable head {fn}"
  | .const name _ =>
    if name == ``letFun && args.size == 4 then
      match args[3]! with
      | .lam n t b _ => return ← proveLet leaves hyps e n t args[2]! b
      | f => throwError "misaWalk: letFun with a non-lambda body {f}"
    if name == ``ite && args.size == 5 then
      let hy ← prove leaves hyps args[3]!
      let hn ← prove leaves hyps args[4]!
      let α ← sailArg args[0]!
      return mkAppN (mkConst (lemmaName `misa_ite))
        #[α, args[1]!, args[2]!, args[3]!, args[4]!, hy, hn]
    if name == ``Bind.bind && args.size == 6 then
      let hf ← prove leaves hyps args[4]!
      let hr ← withLocalDeclD `value args[2]! fun value => do
        mkLambdaFVars #[value] (← prove leaves hyps (mkApp args[5]! value))
      return mkAppN (mkConst (lemmaName `misa_bind))
        #[args[2]!, args[3]!, args[4]!, args[5]!, hf, hr]
    if (← isMatcher name) then
      match ← reduceMatcher? e with
      | .reduced e' => return ← prove leaves hyps e'
      | _ => pure ()
      let some info ← getMatcherInfo? name | throwError "misaWalk: no matcher info for {name}"
      let i := info.numParams + 1
      unless info.numDiscrs == 1 && i < args.size do
        throwError "misaWalk: matcher {name} with {info.numDiscrs} discriminants is unsupported"
      let x := args[i]!
      unless x.isFVar do throwError "misaWalk: matcher {name} on a non-variable {x}"
      let xTy ← inferType x
      unless xTy.isAppOfArity ``Option 1 do
        throwError "misaWalk: matcher {name} on a non-Option type {xTy}"
      let T := xTy.appArg!
      let γ ← sailArg (← inferType e)
      -- `Option.casesOn` on the discriminant, with the matcher kept as the motive's body
      let motive := Expr.lam `d xTy
        (mkApp (mkConst ``MisaOnly) γ |>.app (mkAppN fn (args.set! i (.bvar 0)))) .default
      let noneE := mkAppN fn (args.set! i (mkApp (mkConst ``Option.none [Level.zero]) T))
      let pNone ← match ← reduceMatcher? noneE with
        | .reduced r => prove leaves hyps r
        | _ => throwError "misaWalk: the none branch of {name} does not reduce"
      let pSome ← withLocalDeclD `r T fun r => do
        let someE := mkAppN fn (args.set! i (mkApp2 (mkConst ``Option.some [Level.zero]) T r))
        let pf ← match ← reduceMatcher? someE with
          | .reduced r' => prove leaves hyps r'
          | _ => throwError "misaWalk: the some branch of {name} does not reduce"
        mkLambdaFVars #[r] pf
      return mkAppN (mkConst ``Option.casesOn [Level.zero, Level.zero])
        #[T, motive, x, pNone, pSome]
    match ← leaves name args with
    | some pf => return pf
    | none => throwError "misaWalk: no rule for head {name} ({args.size} arguments)"
  | _ => throwError "misaWalk: unsupported head {fn}"

/-- `let n : t := v; b` (also `letFun v (fun n => b)`). A function-valued `v` is a join point:
    its proof is `joined`, its uses in `b` go through the hypothesis `hj`. Other values are
    bound as a local and the proof is applied to `v`. -/
partial def proveLet (leaves : Leaves) (hyps : List (Expr × Expr)) (e : Expr)
    (n : Name) (t : Expr) (v : Expr) (b : Expr) : MetaM Expr := do
  if v.isLambda then
    let α := v.bindingDomain!
    let (β, sail) ← withLocalDeclD `x α fun x => do
      let ty := (← inferType (mkApp v x)).headBeta
      unless ty.isApp do throwError "misaWalk: join point of non-monadic type {ty}"
      return (ty.appArg!, ty.appFn!)
    let γ ← sailArg (← inferType e)
    let joined ← withLocalDeclD `x α fun x => do
      mkLambdaFVars #[x] (← prove leaves hyps (mkApp v x))
    let jTy := Expr.forallE `x α (mkApp sail β) .default
    let rest ← withLocalDeclD `j jTy fun j => do
      let hjTy := Expr.forallE `x α
        (mkApp2 (mkConst ``MisaOnly) β (mkApp j (.bvar 0))) .default
      withLocalDeclD `hj hjTy fun hj => do
        let pf ← prove leaves ((j, hj) :: hyps) (b.instantiate1 j)
        mkLambdaFVars #[j, hj] pf
    let body ← withLocalDeclD n jTy fun j => mkLambdaFVars #[j] (b.instantiate1 j)
    return mkAppN (mkConst (lemmaName `misa_join)) #[α, β, γ, v, body, joined, rest]
  else
    withLocalDeclD n t fun x => do
      let pf ← prove leaves hyps (b.instantiate1 x)
      return mkApp (← mkLambdaFVars #[x] pf) v

end

end Walk

open Lean Elab Tactic in
/-- Closes `MisaOnly e` for the goal's decoder body `e` (unfold the decoder first). -/
elab "misa_walk" : tactic => do
  let g ← getMainGoal
  let pf ← Walk.prove Walk.decoderLeaves [] (← g.getType).appArg!
  g.assign pf
  replaceMainGoal []

end Airbender.Reference.Sail
