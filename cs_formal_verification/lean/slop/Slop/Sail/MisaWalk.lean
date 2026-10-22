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

/-- The registers that successful instruction execution writes (the PC pair and the general registers).
    A decoder reads no state outside them: the full model's decoder reads configuration (`misa`, `vtype`,
    the privilege level, the envcfg registers), so a decoding replays in any state that agrees on everything
    else. -/
def StepRegisters : List SailRV32.Register := [.PC, .nextPC, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- States agree outside the registers a step writes. -/
def ConfigSame (before state : State) : Prop :=
  ∀ register, register ∉ StepRegisters → state.regs.get? register = before.regs.get? register

/-- A property of the existing Sail interpreter: successful execution preserves state and can be
    replayed in any state with the same configuration registers (`ConfigSame`). -/
def MisaOnly {α : Type} (action : SailRV32.SailM α) : Prop :=
  ∀ before value after, run action before = .ok value after →
    after = before ∧ ∀ state, ConfigSame before state →
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

/-- Reading a register outside the step registers is replayable: its value is fixed by `ConfigSame`. -/
theorem read_outside (register : SailRV32.Register) (outside : register ∉ StepRegisters) :
    MisaOnly (SailRV32.readReg register) := by
  intro before value after executed
  cases found : before.regs.get? register with
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
    exact read_register ((equal register outside).trans found)

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

/-- The vector element width, read through `vtype` (the decoder's `get_sew`, even for scalar encodings). -/
theorem misa_get_sew_pow (unit : Unit) : MisaOnly (SailRV32.Functions.get_sew_pow unit) := by
  unfold SailRV32.Functions.get_sew_pow
  repeat' first
    | (apply read_outside; decide)
    | apply misa_pure
    | apply misa_assert
    | apply misa_throw
    | (apply misa_bind <;> try intro)

theorem misa_get_sew (unit : Unit) : MisaOnly (SailRV32.Functions.get_sew unit) := by
  unfold SailRV32.Functions.get_sew
  repeat' first
    | exact misa_get_sew_pow _
    | apply misa_pure
    | (apply misa_bind <;> try intro)

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
      | (apply read_outside; decide)
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

theorem misa_rounding_mode (bits : BitVec 3) :
    MisaOnly (SailRV32.Functions.encdec_rounding_mode_backwards bits) := by
  unfold SailRV32.Functions.encdec_rounding_mode_backwards
  repeat' first
    | apply misa_pure
    | apply misa_assert
    | apply misa_throw
    | (apply misa_bind <;> try intro)
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


/-! Value properties: `Returns P e` says every successful result of `e` satisfies `P`. -/

/-- Every successful result of `action` satisfies `property`. -/
def Returns {α : Type} (property : α → Prop) (action : SailRV32.SailM α) : Prop :=
  ∀ before value after, run action before = .ok value after → property value

/-- `property` on the `some` case, nothing on `none`. -/
def optionProperty {α : Type} (property : α → Prop) : Option α → Prop
  | none => True
  | some value => property value

theorem returns_true {α : Type} (action : SailRV32.SailM α) :
    Returns (fun _ : α => True) action := by
  intro before value after executed
  trivial

theorem ret_pure {α : Type} (property : α → Prop) (value : α) (h : property value) :
    Returns property (pure value) := by
  intro before actual after executed
  exact (EStateM.Result.ok.inj executed).1 ▸ h

theorem ret_bind {α β : Type} (property : β → Prop) (firstProperty : α → Prop)
    (action : SailRV32.SailM α) (next : α → SailRV32.SailM β)
    (hfirst : Returns firstProperty action)
    (hnext : ∀ value, firstProperty value → Returns property (next value)) :
    Returns property (action >>= next) := by
  intro before value after executed
  cases firstRun : run action before with
  | error error middle =>
    rw [run_bind_of_error _ _ _ _ _ firstRun] at executed
    cases executed
  | ok result middle =>
    rw [run_bind_of_ok _ _ _ _ _ firstRun] at executed
    exact hnext result (hfirst before result middle firstRun) middle value after executed

theorem ret_throw {α : Type} (property : α → Prop) (error : _root_.Sail.Error SailRV32.exception) :
    Returns property (throw error : SailRV32.SailM α) := by
  intro before value after executed
  cases executed

theorem ret_ite {α : Type} (property : α → Prop) (condition : Prop) [Decidable condition]
    (yes no : SailRV32.SailM α) (hy : Returns property yes) (hn : Returns property no) :
    Returns property (if condition then yes else no) := by
  by_cases selected : condition <;> simp [selected, hy, hn]

set_option linter.deprecated false in
/-- A join point of a `have` whose value is a function: its results satisfy `property` when its
    argument satisfies `Pa` (`joined`); its uses in the body are through `j` (`rest`). -/
theorem ret_join {α γ : Type} (property : γ → Prop) (Pa : α → Prop) (jp : α → SailRV32.SailM γ)
    (body : (α → SailRV32.SailM γ) → SailRV32.SailM γ)
    (joined : ∀ x, Pa x → Returns property (jp x))
    (rest : ∀ j : α → SailRV32.SailM γ, (∀ x, Pa x → Returns property (j x)) →
      Returns property (body j)) :
    Returns property (letFun jp body) :=
  rest jp joined

attribute [irreducible] Returns

namespace Walk

open Lean Meta Elab Tactic

/-- Leaf table: a proof of the predicate of `head args` for the heads that end a branch. -/
abbrev Leaves := Name → Array Expr → MetaM (Option Expr)

/-- What the walk proves about a term: `MisaOnly` (state-preserving), or `Returns Q` with
    `valueProof Q v` proving `Q v` at a `pure v` leaf. -/
inductive Mode where
  | misa
  | returns (valueProof : Expr → Expr → MetaM Expr)

/-- Walk context. `joins`: join point ↦ proof of `∀ x, P (j x)`. `facts`: a value in scope ↦ proof
    of the property it has (from a bind's first action, or the `some` case of a match). -/
structure Ctx where
  mode : Mode
  leaves : Leaves
  joins : List (Expr × Expr × Bool) := []
  facts : List (Expr × Expr) := []

private def lemmaName (n : Name) : Name := `Airbender.Reference.Sail ++ n

/-- The value type `α` of a `SailM α` type. -/
private def sailArg (t : Expr) : MetaM Expr := do
  let t := t.headBeta
  unless t.isApp do throwError "misaWalk: expected a SailM type, got {t}"
  return t.appArg!

/-- The predicate of the mode on `e : SailM γ`: `MisaOnly γ e`, or `Returns Q e`. -/
private def predOf (ctx : Ctx) (γ Q e : Expr) : Expr :=
  match ctx.mode with
  | .misa => mkAppN (mkConst ``MisaOnly) #[γ, e]
  | .returns _ => mkAppN (mkConst ``Returns) #[γ, Q, e]

/-- `Q` is the trivial property `fun _ => True`: every action satisfies it. -/
private def isTrivialProperty (Q : Expr) : Bool :=
  Q.isLambda && Q.bindingBody!.isConstOf ``True

/-- `ext ∈ l` for a literal list `l` (a `cons` spine), found by position; no decidability needed.
    `none` when `ext` is not in the list. -/
private partial def listMemProofOpt (ext l : Expr) : MetaM (Option Expr) := do
  unless l.isAppOfArity ``List.cons 3 do return none
  let α := l.getArg! 0
  let a := l.getArg! 1
  let rest := l.getArg! 2
  if a == ext then return some (mkAppN (mkConst ``List.Mem.head [Level.zero]) #[α, a, rest])
  let some tail ← listMemProofOpt ext rest | return none
  return some (mkAppN (mkConst ``List.Mem.tail [Level.zero]) #[α, ext, a, rest, tail])

/-- The `misa`-only leaves of the generated decoder and of `assert`/`throw`. -/
def decoderLeaves : Leaves := fun name args => do
  let c (n : Name) := mkConst (lemmaName n)
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
  if name == `SailRV32.readReg && args.size == 1 then
    -- a read of a register the step does not write: `read_outside r` (the proof of `r ∉ StepRegisters` by decide)
    let outside ← inferType (mkApp (c `read_outside) args[0]!)
    return some (mkAppN (c `read_outside) #[args[0]!, ← mkDecideProof outside.bindingDomain!])
  if name == `SailRV32.Functions.encdec_rounding_mode_backwards && args.size == 1 then
    return some (mkAppN (c `misa_rounding_mode) #[args[0]!])
  -- the decoder's helpers: `encdec_<s>_backwards` has its lemma `misa_<s>` (generated, Slop/Sail/MisaHelpers.lean)
  if let some short := (name.toString.dropPrefix? "SailRV32.Functions.encdec_").bind (·.dropSuffix? "_backwards") then
    let lemmaN := lemmaName (Name.mkSimple s!"misa_{short}")
    if args.size == 1 && (← getEnv).contains lemmaN then
      return some (mkAppN (mkConst lemmaN) args)
  -- decoder helper functions: `misa_fn_<f>` (generated, Slop/Sail/MisaFunctions.lean)
  if let some short := name.toString.dropPrefix? "SailRV32.Functions." then
    let lemmaN := lemmaName (Name.mkSimple s!"misa_fn_{short}")
    if (← getEnv).contains lemmaN then
      return some (mkAppN (mkConst lemmaN) args)
  if name == `SailRV32.Functions.get_sew && args.size == 1 then
    return some (mkAppN (c `misa_get_sew) #[args[0]!])
  if name == `SailRV32.Functions.virtual_memory_supported && args.size == 1 then
    return some (c `misa_virtual)
  -- the extension checks: `misa_ce_<Ext>` (generated, Slop/Sail/MisaDecoder.lean)
  if name == `SailRV32.Functions.currentlyEnabled && args.size == 1 then
    if let some x := args[0]!.constName? then
      if let some e := x.toString.dropPrefix? "SailRV32.extension." then
        let lemmaN := lemmaName (Name.mkSimple s!"misa_ce_{e.toString.drop 4}")
        if (← getEnv).contains lemmaN then return some (mkConst lemmaN)
    let lemmaTy ← inferType (mkApp (c `misa_enabled) args[0]!)
    let dom := lemmaTy.bindingDomain!
    match ← listMemProofOpt dom.appArg! dom.appFn!.appArg! with
    | some h => return some (mkAppN (c `misa_enabled) #[args[0]!, h])
    | none =>
      -- not in the list: its clause is `pure (hartSupports ext)` (no misa read), e.g. Zihintpause;
      -- the kernel re-checks that `currentlyEnabled ext` unfolds to this `pure`
      return some (mkAppN (c `misa_pure) #[mkConst ``Bool,
        mkApp (mkConst ``SailRV32.Functions.hartSupports) args[0]!])
  if name == `SailRV32.assert && args.size == 2 then
    return some (mkAppN (c `misa_assert) #[args[0]!, args[1]!])
  if name == ``MonadExcept.throw && args.size == 5 then
    return some (mkAppN (c `misa_throw) #[args[3]!, args[4]!])
  return none

/-- The fact in scope about a value (returns mode): the proof of its `optionProperty`. -/
def factOf (ctx : Ctx) (x : Expr) : MetaM Expr := do
  match ctx.facts.find? (fun p => p.1 == x) with
  | some (_, h) => return h
  | none => throwError "misaWalk: no fact in scope for {x}"

mutual

/-- A proof of the mode's predicate of `e : SailM γ`; `Q` is the property of its result (ignored in
    `misa` mode). Structural: never unfolds a definition and creates no metavariables. -/
partial def prove (ctx : Ctx) (γ Q : Expr) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if e.isHeadBetaTarget then return ← prove ctx γ Q e.headBeta
  if let .letE n t v b _ := e then return ← proveLet ctx γ Q n t v b
  if let .returns _ := ctx.mode then
    if isTrivialProperty Q then return mkAppN (mkConst ``returns_true) #[γ, e]
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .fvar id =>
    match ctx.joins.find? (fun p => p.1.fvarId! == id) with
    | some (_, hj, needFact) =>
      match ctx.mode with
      | .misa => return mkAppN hj args
      | .returns _ =>
        let x := args[0]!
        let pa ← if needFact then factOf ctx x else pure (mkConst ``True.intro)
        return mkAppN hj #[x, pa]
    | none => throwError "misaWalk: free variable head {fn}"
  | .const name _ =>
    if name == ``letFun && args.size == 4 then
      match args[3]! with
      | .lam n t b _ => return ← proveLet ctx γ Q n t args[2]! b
      | f => throwError "misaWalk: letFun with a non-lambda body {f}"
    if name == ``Pure.pure && args.size == 4 then
      match ctx.mode with
      | .misa => return mkAppN (mkConst (lemmaName `misa_pure)) #[args[2]!, args[3]!]
      | .returns _ =>
        return mkAppN (mkConst (lemmaName `ret_pure))
          #[args[2]!, Q, args[3]!, ← valueProof ctx Q args[3]!]
    if name == ``ite && args.size == 5 then
      let α ← sailArg args[0]!
      let hy ← prove ctx γ Q args[3]!
      let hn ← prove ctx γ Q args[4]!
      return match ctx.mode with
        | .misa => mkAppN (mkConst (lemmaName `misa_ite))
            #[α, args[1]!, args[2]!, args[3]!, args[4]!, hy, hn]
        | .returns _ => mkAppN (mkConst (lemmaName `ret_ite))
            #[α, Q, args[1]!, args[2]!, args[3]!, args[4]!, hy, hn]
    if name == ``Bind.bind && args.size == 6 then
      return ← proveBind ctx γ Q args
    if (← isMatcher name) then
      match ← reduceMatcher? e with
      | .reduced e' => return ← prove ctx γ Q e'
      | _ => pure ()
      return ← proveMatch ctx γ Q name fn args
    if name == ``MonadExcept.throw && args.size == 5 then
      if let .returns _ := ctx.mode then
        return mkAppN (mkConst (lemmaName `ret_throw)) #[args[3]!, Q, args[4]!]
    match ← ctx.leaves name args with
    | some pf => return pf
    | none => throwError "misaWalk: no rule for head {name} ({args.size} arguments: {args})"
  | _ => throwError "misaWalk: unsupported head {fn}"

/-- The proof of `Q v` at `pure v`: a fact in scope, the trivial property, or the mode's leaf rule. -/
partial def valueProof (ctx : Ctx) (Q v : Expr) : MetaM Expr := do
  if let some (_, h) := ctx.facts.find? (fun p => p.1 == v) then return h
  if isTrivialProperty Q then return mkConst ``True.intro
  match ctx.mode with
  | .returns f => f Q v
  | .misa => throwError "misaWalk: value property in misa mode"

/-- `action >>= next`. In `returns` mode the first action gets `optionProperty Q` when it returns an
    `Option` of the continuation's type (else nothing), and the continuation gets that as a fact
    about the value it is applied to. -/
partial def proveBind (ctx : Ctx) (γ Q : Expr) (args : Array Expr) : MetaM Expr := do
  let α := args[2]!
  let β := args[3]!
  let action := args[4]!
  let k := args[5]!
  match ctx.mode with
  | .misa =>
    let hf ← prove ctx α Q action
    let hr ← withLocalDeclD `value α fun value => do
      mkLambdaFVars #[value] (← prove ctx γ Q (mkApp k value))
    return mkAppN (mkConst (lemmaName `misa_bind)) #[α, β, action, k, hf, hr]
  | .returns _ =>
    let Qa : Expr ←
      if α.isAppOfArity ``Option 1 && α.appArg! == β then
        pure (mkApp (mkConst ``optionProperty) β |>.app Q)
      else
        pure (Expr.lam `v α (mkConst ``True) .default)
    let hf ← prove ctx α Qa action
    let hr ← withLocalDeclD `value α fun value => do
      withLocalDeclD `hv (mkApp Qa value).headBeta fun hv => do
        let ctx' := { ctx with facts := (value, hv) :: ctx.facts }
        mkLambdaFVars #[value, hv] (← prove ctx' γ Q (mkApp k value))
    return mkAppN (mkConst (lemmaName `ret_bind)) #[α, β, Q, Qa, action, k, hf, hr]

/-- A matcher on a variable of type `Option T`, split by `Option.casesOn`. The motive is the
    matcher with the variable abstracted (and, in `returns` mode, the fact about the variable as
    an antecedent when one is in scope). Each branch is the matcher reduced at the constructor. -/
partial def proveMatch (ctx : Ctx) (γ Q : Expr) (name : Name) (fn : Expr) (args : Array Expr) :
    MetaM Expr := do
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
  let optProp := mkApp (mkConst ``optionProperty) T |>.app Q
  let fact? := ctx.facts.find? (fun p => p.1 == x) |>.map (·.2)
  let withD (d : Expr) : Expr := predOf ctx γ Q (mkAppN fn (args.set! i d))
  let motive : Expr :=
    match fact? with
    | none => Expr.lam `d xTy (withD (.bvar 0)) .default
    | some _ =>
      Expr.lam `d xTy
        (Expr.forallE `h (optProp.app (.bvar 0)) (withD (.bvar 1)) .default) .default
  let noneE := mkAppN fn (args.set! i (mkApp (mkConst ``Option.none [Level.zero]) T))
  let pNone ← match fact? with
    | none => do
      match ← reduceMatcher? noneE with
      | .reduced r => prove ctx γ Q r
      | _ => throwError "misaWalk: the none branch of {name} does not reduce"
    | some _ =>
      withLocalDeclD `hd (optProp.app (mkConst ``Option.none [Level.zero] |>.app T)) fun hd => do
        let r ← match ← reduceMatcher? noneE with
          | .reduced r => prove ctx γ Q r
          | _ => throwError "misaWalk: the none branch of {name} does not reduce"
        mkLambdaFVars #[hd] r
  let pSome ← withLocalDeclD `r T fun r => do
    let someR := mkApp2 (mkConst ``Option.some [Level.zero]) T r
    let someE := mkAppN fn (args.set! i someR)
    let branch (ctx' : Ctx) : MetaM Expr := do
      match ← reduceMatcher? someE with
      | .reduced r' => prove ctx' γ Q r'
      | _ => throwError "misaWalk: the some branch of {name} does not reduce"
    match fact? with
    | none => mkLambdaFVars #[r] (← branch ctx)
    | some _ =>
      withLocalDeclD `hd (optProp.app someR) fun hd => do
        mkLambdaFVars #[r, hd] (← branch { ctx with facts := (r, hd) :: ctx.facts })
  let cases := mkAppN (mkConst ``Option.casesOn [Level.zero, Level.zero])
    #[T, motive, x, pNone, pSome]
  return match fact? with
    | none => cases
    | some hx => mkApp cases hx

/-- `let n : t := v; b`, also `letFun v (fun n => b)`. A function-valued `v` is a join point: its
    results are proven once (`joined`); its uses in `b` go through the hypothesis for `j`. Any other
    value is bound as a local and the proof is applied to `v`. -/
partial def proveLet (ctx : Ctx) (γ Q : Expr) (n : Name) (t v b : Expr) : MetaM Expr := do
  if v.isLambda then
    let α := v.bindingDomain!
    let (β, sail) ← withLocalDeclD `x α fun x => do
      let ty := (← inferType (mkApp v x)).headBeta
      unless ty.isApp do throwError "misaWalk: join point of non-monadic type {ty}"
      return (ty.appArg!, ty.appFn!)
    let jTy := Expr.forallE `x α (mkApp sail β) .default
    -- `returns` mode: a join point of `Option γ` is used on a value with the fact `optionProperty Q`
    let needFact := match ctx.mode with
      | .misa => false
      | .returns _ => α.isAppOfArity ``Option 1 && α.appArg! == γ
    let Pa : Expr := if needFact then mkApp (mkConst ``optionProperty) γ |>.app Q
      else Expr.lam `x α (mkConst ``True) .default
    let paOf (x : Expr) : Expr := (mkApp Pa x).headBeta
    let joined ← withLocalDeclD `x α fun x => do
      match ctx.mode with
      | .misa => mkLambdaFVars #[x] (← prove ctx β Q (mkApp v x))
      | .returns _ =>
        withLocalDeclD `hx (paOf x) fun hx => do
          let ctx' := if needFact then { ctx with facts := (x, hx) :: ctx.facts } else ctx
          mkLambdaFVars #[x, hx] (← prove ctx' β Q (mkApp v x))
    let rest ← withLocalDeclD `j jTy fun j => do
      let hjTy := match ctx.mode with
        | .misa => Expr.forallE `x α (predOf ctx β Q (mkApp j (.bvar 0))) .default
        | .returns _ =>
          Expr.forallE `x α
            (Expr.forallE `hx (paOf (.bvar 0)) (predOf ctx β Q (mkApp j (.bvar 1))) .default)
            .default
      withLocalDeclD `hj hjTy fun hj => do
        let pf ← prove { ctx with joins := (j, hj, needFact) :: ctx.joins } γ Q (b.instantiate1 j)
        mkLambdaFVars #[j, hj] pf
    let body ← withLocalDeclD n jTy fun j => mkLambdaFVars #[j] (b.instantiate1 j)
    match ctx.mode with
    | .misa =>
      return mkAppN (mkConst (lemmaName `misa_join)) #[α, β, γ, v, body, joined, rest]
    | .returns _ =>
      unless β == γ do throwError "misaWalk: join point result {β} differs from {γ}"
      return mkAppN (mkConst (lemmaName `ret_join)) #[α, γ, Q, Pa, v, body, joined, rest]
  else
    withLocalDeclD n t fun x => do
      let pf ← prove ctx γ Q (b.instantiate1 x)
      return mkApp (← mkLambdaFVars #[x] pf) v

end

/-- Proves `goal`'s predicate for the decoder body `e`, with the mode and leaves given. -/
def proveGoal (ctx : Ctx) (γ Q e : Expr) : MetaM Expr := prove ctx γ Q e

end Walk

open Lean Elab Tactic in
/-- Closes `MisaOnly γ e` for the goal's decoder body `e` (unfold the decoder first). -/
elab "misa_walk" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  let pf ← Walk.proveGoal { mode := .misa, leaves := Walk.decoderLeaves } (ty.getArg! 0) (mkConst ``True) ty.appArg!
  g.assign pf
  replaceMainGoal []

end Airbender.Reference.Sail
