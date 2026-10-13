import Slop.Equiv.Slice
import Slop.Sail.Oracle
import Slop.Equiv.Hints

/-! `walk_decoder hs`: run Sail's decoder (a chain of ~400 clauses) on a word of which only some bits are known
(`Bits w lo n k` hypotheses), clause by clause, without ever simplifying the rest of the chain:
* a clause whose guard is false (decided from the known bits, `Slice.lean`) is skipped: by `run_ite_false`, the
  clause is `pure none >>= jp`, i.e. the rest of the chain;
* `currentlyEnabled X` is answered once per extension by a closed kernel computation (`en_run`, valid on every
  `Sys` state);
* it stops at the first clause whose guard is true, leaving that clause's body as the goal.
Each step looks only at the head of the goal and at one guard, so a walk costs the same per clause however long
the decoder is. -/

open Lean Meta Elab Tactic
open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

theorem run_ite_false {α : Type} {G : Bool} {A B : SailM α} {σ : FState} {r} (hG : G = false)
    (h : runF B σ = r) : runF (if G = true then A else B) σ = r := by
  subst hG; exact h
theorem run_ite_true {α : Type} {G : Bool} {A B : SailM α} {σ : FState} {r} (hG : G = true)
    (h : runF A σ = r) : runF (if G = true then A else B) σ = r := by
  subst hG; exact h
theorem run_pure_bind {α β : Type} (a : α) (f : α → SailM β) (σ : FState) {r} (h : runF (f a) σ = r) :
    runF (pure a >>= f) σ = r := by
  rw [runF_bind_ok _ f σ σ a (runF_pure a σ)]; exact h
theorem run_bind_ok {α β : Type} (m : SailM α) (f : α → SailM β) (σ : FState) (a : α) {r}
    (hm : runF m σ = .ok a σ) (h : runF (f a) σ = r) : runF (m >>= f) σ = r := by
  rw [runF_bind_ok m f σ σ a hm]; exact h

theorem run_eq_pure_bind {α β : Type} (m : SailM α) (a : α) (f : α → SailM β) (σ : FState) {r}
    (hm : m = pure a) (h : runF (f a) σ = r) : runF (m >>= f) σ = r := by
  subst hm; exact run_pure_bind a f σ h

theorem run_bind_assoc {α β γ : Type} (m : SailM α) (f : α → SailM β) (g : β → SailM γ) (σ : FState) {r}
    (h : runF (m >>= fun x => f x >>= g) σ = r) : runF ((m >>= f) >>= g) σ = r := by
  rw [← h]
  simp only [runF_bind]
  cases runF m σ <;> rfl
theorem run_bind_ite_false {α β : Type} {G : Bool} {A B : SailM α} (g : α → SailM β) {σ : FState} {r}
    (hG : G = false) (h : runF (B >>= g) σ = r) : runF ((if G = true then A else B) >>= g) σ = r := by
  subst hG; exact h
theorem run_bind_ite_true {α β : Type} {G : Bool} {A B : SailM α} (g : α → SailM β) {σ : FState} {r}
    (hG : G = true) (h : runF (A >>= g) σ = r) : runF ((if G = true then A else B) >>= g) σ = r := by
  subst hG; exact h

theorem run_bind_pure_ex {α β : Type} (m : SailM α) (k : α → SailM β) (σ : FState) {r}
    (hm : ∃ a, m = pure a) (h : ∀ a, runF (k a) σ = r) : runF (m >>= k) σ = r := by
  obtain ⟨a, rfl⟩ := hm; exact run_pure_bind a k σ (h a)
theorem run_ite_undec {α β : Type} {G : Bool} (body : SailM (Option α)) (jp : Option α → SailM β) {σ : FState}
    {r} (hb : G = true → runF body σ = .ok none σ) (h : runF (jp none) σ = r) :
    runF (if G = true then body >>= jp else pure none >>= jp) σ = r := by
  cases hG : G
  · exact run_pure_bind none jp σ h
  · exact run_bind_ok body jp σ none (hb hG) h
theorem and_left {x y : Bool} (h : (x && y) = true) : x = true := by simp_all
theorem and_right {x y : Bool} (h : (x && y) = true) : y = true := by simp_all

theorem known_sys {σ : FState} (hs : Airbender.Sys σ) : ∀ r v, knownDemo r = some v → σ.regs r = v := by
  intro r v h
  unfold knownDemo at h
  split at h
  · simp at h
  · rename_i hv
    cases h
    exact hs r (by simpa using hv)

/-- `currentlyEnabled X` on any Airbender state, from one closed computation. -/
theorem en_run {σ : FState} (hs : Airbender.Sys σ) (X : extension) (b : Bool)
    (h : runOracle knownDemo (fun _ => none) (currentlyEnabled X) = some b) :
    runF (currentlyEnabled X) σ = .ok b σ :=
  runOracle_sound knownDemo (fun _ => none) σ h (known_sys hs) (fun _ _ h => by simp at h)

theorem and_false_r {x y : Bool} (h : y = false) : (x && y) = false := by subst h; simp
theorem and_false_l {x y : Bool} (h : x = false) : (x && y) = false := by subst h; simp
theorem and_true' {x y : Bool} (h1 : x = true) (h2 : y = true) : (x && y) = true := by subst h1 h2; rfl
theorem or_true_l {x y : Bool} (h : x = true) : (x || y) = true := by subst h; simp
theorem or_true_r {x y : Bool} (h : y = true) : (x || y) = true := by subst h; simp
theorem or_false' {x y : Bool} (h1 : x = false) (h2 : y = false) : (x || y) = false := by subst h1 h2; rfl
theorem not_eq' {x : Bool} (b : Bool) (h : x = b) : (!x) = !b := by subst h; rfl

/-- Known bits of the word: `Bits w lo n k` hypotheses in the local context. -/
structure Fact where
  lo : Nat
  n : Nat
  k : Nat
  pf : Expr

def getFacts : MetaM (Array Fact) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Bits 4 then
      let some lo ← (evalNat (ty.getArg! 1)).run | continue
      let some n ← (evalNat (ty.getArg! 2)).run | continue
      let some k ← (evalNat (ty.getArg! 3)).run | continue
      out := out.push { lo, n, k, pf := d.toExpr }
  return out

/-- A closed proposition, proven by the kernel. -/
def kernelDecideImpl (p : Expr) : MetaM Expr := do
  let mv ← mkFreshExprSyntheticOpaqueMVar p
  let gs ← withOptions (fun o => maxRecDepth.set o 1000000) <|
    Elab.Term.TermElabM.run' <| Tactic.run mv.mvarId! (evalTactic (← `(tactic| decide +kernel)))
  unless gs.isEmpty do throwError "kernelDecide: could not decide {p}"
  instantiateMVars mv

def kernelDecide (p : Expr) : MetaM Expr := kernelDecideImpl p

def natLit (n : Nat) : Expr := mkNatLit n

/-- The known value of bits `[lo, lo + n)`, if they lie inside one known fact. -/
def exactFact (facts : Array Fact) (lo n : Nat) : MetaM (Option Fact) := do
  for f in facts do
    if f.lo == lo && f.n == n then return some f
  for f in facts do
    if f.lo ≤ lo && lo + n ≤ f.lo + f.n then
      let h1 ← mkDecideProof (← mkAppM ``LE.le #[natLit f.lo, natLit lo])
      let h2 ← mkDecideProof (← mkAppM ``LE.le #[natLit (lo + n), natLit (f.lo + f.n)])
      let pf ← mkAppM ``bits_sub #[natLit lo, natLit n, f.pf, h1, h2]
      let k := (f.k >>> (lo - f.lo)) % 2 ^ n
      -- normalise the value to a literal
      let ty ← mkAppM ``Bits #[(← inferType f.pf).getArg! 0, natLit lo, natLit n, natLit k]
      return some { lo, n, k, pf := ← mkExpectedTypeHint pf ty }
  return none

/-- Decide `extractLsb w hi lo == c` (or `w == c` when `hi = 31`, `lo = 0`, `whole`) from the facts. -/
def evalSlice (facts : Array Fact) (lhs c : Expr) (hi lo : Nat) (whole : Bool) :
    MetaM (Option (Bool × Expr)) := do
  let some ⟨_, cv⟩ ← getBitVecValue? c | return none
  let cn := cv.toNat
  if let some f ← exactFact facts lo (hi - lo + 1) then
    let facts := #[f]
    if f.k == cn && !whole then
      let pf ← mkExpectedTypeHint f.pf (← mkAppM ``Bits #[lhs.getArg! 1, natLit lo, natLit (hi - lo + 1),
        ← mkAppM ``BitVec.toNat #[c]])
      return some (true, ← mkAppOptM ``slice_beq_true #[lhs.getArg! 1, natLit hi, natLit lo, c, pf])
    if f.k != cn then
      let hc ← mkDecideProof (mkNot (← mkEq (← mkAppM ``HMod.hMod #[← mkAppM ``HShiftRight.hShiftRight
        #[← mkAppM ``BitVec.toNat #[c], natLit 0], ← mkAppM ``HPow.hPow #[natLit 2, natLit f.n]]) (natLit f.k)))
      if whole then
        return some (false, ← mkAppM ``word_beq_false #[natLit f.lo, natLit f.n, natLit f.k, f.pf, hc])
      let hlo ← mkDecideProof (← mkAppM ``LE.le #[natLit lo, natLit f.lo])
      let hhi ← mkDecideProof (← mkAppM ``LE.le #[natLit (f.lo + f.n), natLit (hi + 1)])
      return some (false, ← mkAppOptM ``slice_beq_false
        #[lhs.getArg! 1, natLit hi, natLit lo, c, natLit f.lo, natLit f.n, natLit f.k, f.pf, hlo, hhi, hc])
  for f in facts do
    if lo ≤ f.lo && f.lo + f.n ≤ hi + 1 then
      if (cn >>> (f.lo - lo)) % 2 ^ f.n ≠ f.k then
        let hc ← mkDecideProof (mkNot (← mkEq (← mkAppM ``HMod.hMod #[← mkAppM ``HShiftRight.hShiftRight
          #[← mkAppM ``BitVec.toNat #[c], natLit (f.lo - lo)], ← mkAppM ``HPow.hPow #[natLit 2, natLit f.n]])
          (natLit f.k)))
        if whole then
          return some (false, ← mkAppM ``word_beq_false #[natLit f.lo, natLit f.n, natLit f.k, f.pf, hc])
        let hlo ← mkDecideProof (← mkAppM ``LE.le #[natLit lo, natLit f.lo])
        let hhi ← mkDecideProof (← mkAppM ``LE.le #[natLit (f.lo + f.n), natLit (hi + 1)])
        return some (false, ← mkAppOptM ``slice_beq_false
          #[lhs.getArg! 1, natLit hi, natLit lo, c, natLit f.lo, natLit f.n, natLit f.k, f.pf, hlo, hhi, hc])
  -- fully known and equal
  if !whole then
    for f in facts do
      if f.lo == lo && f.n == hi - lo + 1 && f.k == cn then
        let pf ← mkExpectedTypeHint f.pf (← mkAppM ``Bits #[lhs.getArg! 1, natLit lo, natLit (hi - lo + 1),
          ← mkAppM ``BitVec.toNat #[c]])
        return some (true, ← mkAppOptM ``slice_beq_true #[lhs.getArg! 1, natLit hi, natLit lo, c, pf])
  return none

/-- Replace every fully known slice `extractLsb w hi lo` in `e` by its literal: `(e', proof of e = e')`. -/
def substKnown (facts : Array Fact) (e : Expr) : MetaM (Expr × Option Expr) := do
  let mut e := e
  let mut pf : Option Expr := none
  let ref ← IO.mkRef (#[] : Array Expr)
  forEachExpr e fun x => do
    if x.isAppOfArity ``Sail.BitVec.access 3 && (x.getArg! 1).isAppOfArity ``Sail.BitVec.extractLsb 4 then
      ref.modify (·.push x)
  for x in ← ref.get do
    -- `access (extractLsb w hi lo) i`: one known bit
    let s := x.getArg! 1
    let some hi ← (evalNat (s.getArg! 2)).run | continue
    let some lo ← (evalNat (s.getArg! 3)).run | continue
    let some i ← (evalNat (x.getArg! 2)).run | continue
    unless i < hi - lo + 1 do continue
    let some f ← exactFact facts (lo + i) 1 | continue
    let hfact ← mkExpectedTypeHint f.pf (← mkAppM ``Bits #[s.getArg! 1, ← mkAppM ``HAdd.hAdd #[s.getArg! 3, x.getArg! 2],
      natLit 1, natLit f.k])
    let hi' ← mkDecideProof (← mkAppM ``LT.lt #[x.getArg! 2, ← mkAppM ``HAdd.hAdd #[← mkAppM ``HSub.hSub
      #[s.getArg! 2, s.getArg! 3], natLit 1]])
    let hx ← mkAppOptM ``access_slice_lit #[s.getArg! 1, s.getArg! 2, s.getArg! 3, x.getArg! 2, natLit f.k, hfact, hi']
    let lit := mkApp2 (mkConst ``BitVec.ofNat) (natLit 1) (mkNatLit f.k)
    let ty ← inferType x
    let motive ← kabstract e x
    unless motive.hasLooseBVars do continue
    let step ← mkCongrArg (.lam `y ty motive .default) hx
    pf := some (← match pf with | some p => mkEqTrans p step | none => pure step)
    e := motive.instantiate1 lit
  let ref ← IO.mkRef (#[] : Array Expr)
  forEachExpr e fun x => do
    if x.isAppOfArity ``Sail.BitVec.extractLsb 4 then ref.modify (·.push x)
  let occs ← ref.get
  for x in occs do
    let some hi ← (evalNat (x.getArg! 2)).run | continue
    let some lo ← (evalNat (x.getArg! 3)).run | continue
    let some f ← exactFact facts lo (hi - lo + 1) | continue
    let ty ← inferType x
    let width := ty.appArg!
    let lit := mkApp2 (mkConst ``BitVec.ofNat) width (mkNatLit f.k)
    let hx ← mkAppOptM ``slice_eq_lit #[x.getArg! 1, x.getArg! 2, x.getArg! 3, mkNatLit f.k, f.pf]
    let motive ← kabstract e x
    unless motive.hasLooseBVars do continue
    let e' := motive.instantiate1 lit
    let step ← mkCongrArg (.lam `y ty motive .default) hx
    pf := some (← match pf with | some p => mkEqTrans p step | none => pure step)
    e := e'
  return (e, pf)

/-- Decide a Bool guard `G`: `some (b, proof of G = b)`, or `none` if the known bits do not decide it. -/
partial def evalGuard (facts : Array Fact) (G : Expr) : MetaM (Option (Bool × Expr)) := do
  let G ← whnfCore G
  if G.isConstOf ``Bool.true then return some (true, ← mkEqRefl G)
  if G.isConstOf ``Bool.false then return some (false, ← mkEqRefl G)
  if G.isAppOfArity ``Bool.and 2 then
    let (x, y) := (G.getArg! 0, G.getArg! 1)
    if let some (false, py) ← evalGuard facts y then return some (false, ← mkAppOptM ``and_false_r #[x, y, py])
    match ← evalGuard facts x with
    | some (false, px) => return some (false, ← mkAppOptM ``and_false_l #[x, y, px])
    | some (true, px) =>
      if let some (true, py) ← evalGuard facts y then return some (true, ← mkAppOptM ``and_true' #[x, y, px, py])
      return none
    | _ => return none
  if G.isAppOfArity ``Bool.or 2 then
    let (x, y) := (G.getArg! 0, G.getArg! 1)
    match ← evalGuard facts x with
    | some (true, px) => return some (true, ← mkAppOptM ``or_true_l #[x, y, px])
    | some (false, px) =>
      match ← evalGuard facts y with
      | some (true, py) => return some (true, ← mkAppOptM ``or_true_r #[x, y, py])
      | some (false, py) => return some (false, ← mkAppOptM ``or_false' #[x, y, px, py])
      | none => return none
    | none =>
      if let some (true, py) ← evalGuard facts y then return some (true, ← mkAppOptM ``or_true_r #[x, y, py])
      return none
  if G.isAppOfArity ``Bool.not 1 then
    if let some (b, p) ← evalGuard facts (G.getArg! 0) then
      return some (!b, ← mkAppOptM ``not_eq' #[G.getArg! 0, toExpr b, p])
    return none
  if G.isAppOfArity ``BEq.beq 4 then
    let (lhs, c) := (G.getArg! 2, G.getArg! 3)
    let lhs' ← whnfCore lhs
    if lhs'.isAppOfArity ``Sail.BitVec.extractLsb 4 then
      let some hi ← (evalNat (lhs'.getArg! 2)).run | return none
      let some lo ← (evalNat (lhs'.getArg! 3)).run | return none
      if let some r ← evalSlice facts lhs' c hi lo false then
        return some (r.1, ← mkExpectedTypeHint r.2 (← mkEq G (toExpr r.1)))
    else if (← inferType lhs') == mkApp (mkConst ``BitVec) (mkNatLit 32) && lhs'.isFVar then
      if let some r ← evalSlice facts lhs' c 31 0 true then
        return some (r.1, ← mkExpectedTypeHint r.2 (← mkEq G (toExpr r.1)))
  -- anything else (e.g. `encdec_uop_backwards_matches (extractLsb w 6 0)`): put in the known slices, then reduce
  let (G, pSub) ← substKnown facts G
  let r ← withTransparency .default <| whnf G
  for b in [true, false] do
    if r.isConstOf (if b then ``Bool.true else ``Bool.false) then
      let p ← mkExpectedTypeHint (← mkEqRefl (toExpr b)) (← mkEq G (toExpr b))
      return some (b, ← match pSub with | some ps => mkEqTrans ps p | none => pure p)
  return none

/-- `fun _ => none : Nat → Option (BitVec 8)` (no memory is known). -/
def mkFunUnit : MetaM Expr :=
  return .lam `_ (mkConst ``Nat) (mkApp (mkConst ``Option.none [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))) .default

/-- Head of `runF M σ = r` goals. -/
def splitGoal (g : MVarId) : MetaM (Expr × Expr × Expr) := do
  let t ← whnfR (← g.getType)
  let some (_, lhs, r) := t.eq? | throwError "walk_decoder: goal is not an equation"
  unless lhs.isAppOfArity ``runF 3 do throwError "walk_decoder: lhs is not `runF m σ`"
  return (lhs.getArg! 1, lhs.getArg! 2, r)

/-- One proof step: `g := lemma args… ?next`; returns `?next`. -/
def step1 (g : MVarId) (lem : Name) (args : Array (Option Expr)) : MetaM MVarId := do
  let e ← mkAppOptM lem args
  let ty ← inferType e
  let .forallE _ dom _ _ := ty | throwError "step1"
  let next ← mkFreshExprSyntheticOpaqueMVar dom
  g.assign (mkApp e next)
  return next.mvarId!

/-- Hint field decoders: (decoder, its `_matches` test, lemma "valid ⇒ plain value"). -/
def hintHelpers : List (Name × Name × Name) :=
  [(``encdec_ntl_backwards, ``encdec_ntl_backwards_matches, ``ntl_pure),
   (``encdec_cbop_zicbop_backwards, ``encdec_cbop_zicbop_backwards_matches, ``cbop_pure)]

/-- From `pG : G = true`, a proof of `a = true` for a conjunct `a` of `G` satisfying `pred`. -/
partial def findConj (pred : Expr → MetaM Bool) (G pG : Expr) : MetaM (Option Expr) := do
  let G ← whnfCore G
  if ← pred G then return some (← mkExpectedTypeHint pG (← mkEq G (toExpr true)))
  if G.isAppOfArity ``Bool.and 2 then
    let (x, y) := (G.getArg! 0, G.getArg! 1)
    if let some p ← findConj pred x (← mkAppOptM ``and_left #[x, y, pG]) then return some p
    return ← findConj pred y (← mkAppOptM ``and_right #[x, y, pG])
  return none

structure Ctx where
  facts : Array Fact
  hs : Expr
  survey : Bool
  cache : IO.Ref (Std.HashMap Name (Bool × Expr))
  /-- guards known to hold (inside a clause body): `G = true` proofs -/
  hyps : Array Expr := #[]

mutual
/-- Walk the goal `runF M σ = r` as far as possible; returns the remaining goal and the clauses skipped. -/
partial def walkLoop (ctx : Ctx) (g0 : MVarId) : MetaM (MVarId × Nat) := do
  let mut g := g0
  let mut skipped : Nat := 0
  for _ in [0:100000] do
    let (M, σ, r) ← g.withContext (splitGoal g)
    -- unfold the decoder itself, then let/beta/match at the head
    let M ← do
      let M' ← whnfCore M
      if M'.isAppOf ``ext_decode || M'.isAppOf ``encdec_backwards then
        let some M'' ← delta? M' (fun n => n == ``ext_decode || n == ``encdec_backwards) | pure M'
        let M'' ← whnfCore M''
        if M''.isAppOf ``encdec_backwards then
          let some M3 ← delta? M'' (· == ``encdec_backwards) | pure M''
          pure (← whnfCore M3)
        else pure M''
      else pure M'
    g ← g.replaceTargetDefEq (← g.withContext (mkEq (← mkAppM ``runF #[M, σ]) r))
    if M.isAppOfArity ``ite 5 then
      let some (_, G, _) := (M.getArg! 1).eq? | break
      match ← g.withContext (evalGuard ctx.facts G) with
      | some (false, pG) =>
        g ← g.withContext (step1 g ``run_ite_false #[none, G, M.getArg! 3, M.getArg! 4, σ, r, pG])
        skipped := skipped + 1
      | some (true, pG) =>
        g ← g.withContext (step1 g ``run_ite_true #[none, G, M.getArg! 3, M.getArg! 4, σ, r, pG])
      | none =>
        if let some g' ← g.withContext (bodyNone ctx g M σ r G) then
          g := g'; skipped := skipped + 1
        else
          unless ctx.survey do throwError "walk_decoder: undecided guard after {skipped} clauses:{indentExpr G}"
          logInfo m!"survey: undecided guard after {skipped} clauses:{indentExpr G}"
          let pG ← mkSorry (← mkEq G (toExpr false)) false
          g ← g.withContext (step1 g ``run_ite_false #[none, G, M.getArg! 3, M.getArg! 4, σ, r, pG])
          skipped := skipped + 1
    else if M.isAppOfArity ``Bind.bind 6 then
      let (m, f) := (M.getArg! 4, M.getArg! 5)
      let m' ← whnfCore m
      if m'.isAppOfArity ``Pure.pure 4 then
        g ← g.withContext (step1 g ``run_pure_bind #[none, none, m'.getArg! 3, f, σ, r])
      else if m'.isAppOfArity ``Bind.bind 6 then
        g ← g.withContext (step1 g ``run_bind_assoc #[none, none, none, m'.getArg! 4, m'.getArg! 5, f, σ, r])
      else if m'.isAppOfArity ``ite 5 then
        let some (_, G, _) := (m'.getArg! 1).eq? | break
        match ← g.withContext (evalGuard ctx.facts G) with
        | some (false, pG) =>
          g ← g.withContext (step1 g ``run_bind_ite_false #[none, none, G, m'.getArg! 3, m'.getArg! 4, f, σ, r, pG])
          skipped := skipped + 1
        | some (true, pG) =>
          g ← g.withContext (step1 g ``run_bind_ite_true #[none, none, G, m'.getArg! 3, m'.getArg! 4, f, σ, r, pG])
        | none =>
          unless ctx.survey do throwError "walk_decoder: undecided guard after {skipped} clauses:{indentExpr G}"
          logInfo m!"survey: undecided guard after {skipped} clauses:{indentExpr G}"
          let pG ← mkSorry (← mkEq G (toExpr false)) false
          g ← g.withContext (step1 g ``run_bind_ite_false #[none, none, G, m'.getArg! 3, m'.getArg! 4, f, σ, r, pG])
          skipped := skipped + 1
      else if m'.isAppOfArity ``currentlyEnabled 1 then
        let X := m'.getArg! 0
        let key := X.getAppFn.constName?.getD `_
        let (b, pb) ← match (← ctx.cache.get).get? key with
          | some v => pure v
          | none => g.withContext do
            let mut res : Option (Bool × Expr) := none
            for b in [true, false] do
              let p ← mkEq (← mkAppM ``runOracle #[mkConst ``knownDemo, ← mkFunUnit, m']) (← mkAppM ``Option.some #[toExpr b])
              try res := some (b, ← kernelDecide p); break catch _ => pure ()
            let some v := res | throwError "walk_decoder: cannot evaluate {m'}"
            pure v
        ctx.cache.modify (·.insert key (b, pb))
        let hm ← g.withContext (mkAppM ``en_run #[ctx.hs, X, toExpr b, pb])
        g ← g.withContext (step1 g ``run_bind_ok #[none, none, m', f, σ, toExpr b, r, hm])
      else
        -- a small helper (e.g. `encdec_reg_backwards x`): reduce it to `pure a` if it is one
        let (mSub, pSub) ← g.withContext (substKnown ctx.facts m')
        let m'' ← withTransparency .default <| whnf mSub
        if m''.isAppOf ``Sail.ArchSem.FreeM.pure then
          let a := m''.appArg!
          let hm ← g.withContext do
            let pa ← mkAppOptM ``Pure.pure #[M.getArg! 0, none, none, a]
            let p ← mkExpectedTypeHint (← mkEqRefl mSub) (← mkEq mSub pa)
            match pSub with | some ps => mkEqTrans ps p | none => pure p
          g ← g.withContext (step1 g ``run_eq_pure_bind #[none, none, m', a, f, σ, r, hm])
        else
          -- a hint field decoder, valid by a guard we are inside of
          let some (_, mname, lem) := hintHelpers.find? (fun (h, _, _) => m'.isAppOf h) | break
          let x := m'.appArg!
          let mut pm : Option Expr := none
          for h in ctx.hyps do
            let some (_, Gh, _) := (← inferType h).eq? | continue
            if let some p ← g.withContext (findConj (fun a => do
                pure (a.isAppOf mname) <&&> isDefEq a.appArg! x) Gh h) then
              pm := some p; break
          let some pmatch := pm | break
          let hm ← g.withContext (mkAppM lem #[x, pmatch])
          let g1 ← g.withContext (step1 g ``run_bind_pure_ex #[none, none, m', f, σ, r, hm])
          let (_, g2) ← g1.intro1
          g := g2
    else break
  return (g, skipped)

/-- An undecided guard `G` of a clause `if G then body >>= jp else pure none >>= jp`: prove that `body` returns
`none` whenever `G` holds (a hint whose extension is off), so the clause is skipped either way. -/
partial def bodyNone (ctx : Ctx) (g : MVarId) (M σ r G : Expr) : MetaM (Option MVarId) := do
  let A ← whnfCore (M.getArg! 3)
  unless A.isAppOfArity ``Bind.bind 6 do return none
  let (body, jp) := (A.getArg! 4, A.getArg! 5)
  let bodyTy ← inferType body
  let optTy := bodyTy.appArg!
  let noneE ← mkAppOptM ``Option.none #[optTy.appArg!]
  let ε := (← inferType r).getArg! 0
  let rhs ← mkAppOptM ``EStateM.Result.ok #[ε, none, optTy, noneE, σ]
  let hbTy ← withLocalDeclD `hG (← mkEq G (toExpr true)) fun hG => do
    mkForallFVars #[hG] (← mkEq (← mkAppM ``runF #[body, σ]) rhs)
  let hbMv ← mkFreshExprSyntheticOpaqueMVar hbTy
  let (hG, g1) ← hbMv.mvarId!.intro1
  let ok ← g1.withContext do
    try
      let (g2, _) ← walkLoop { ctx with hyps := ctx.hyps.push (mkFVar hG) } g1
      g2.withContext do
        let (M2, _, _) ← splitGoal g2
        let M2 ← whnfCore M2
        unless M2.isAppOfArity ``Pure.pure 4 do return false
        let pf ← mkAppM ``runF_pure #[M2.getArg! 3, σ]
        unless ← isDefEq (← inferType pf) (← g2.getType) do return false
        g2.assign pf
        return true
    catch _ => return false
  unless ok do return none
  return some (← step1 g ``run_ite_undec #[none, none, G, body, jp, σ, r, hbMv])
end

def walkDecoder (hs : Syntax) (survey : Bool) : TacticM Unit := withMainContext do
  let hs ← elabTerm hs none
  let facts ← getFacts
  let cache ← IO.mkRef {}
  let (g, skipped) ← walkLoop { facts, hs, survey, cache } (← getMainGoal)
  replaceMainGoal [g]
  logInfo m!"walk_decoder: skipped {skipped} clauses"

elab "walk_decoder " hs:term : tactic => walkDecoder hs false
/-- Exploration only (uses `sorry`): log undecided guards and treat them as false. -/
elab "walk_decoder_survey " hs:term : tactic => walkDecoder hs true

end Slop.Equiv
