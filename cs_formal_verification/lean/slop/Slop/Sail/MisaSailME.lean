import Slop.Sail.MisaWalk

/-! `MisaOnly` through Sail's early-return layer (`SailME`, run by `SailME.run`): an early return is a value
(`runE`), so the walk's rules carry over (pure, bind, lift, ite, return), and a bind whose first action only
returns values satisfying a property needs its continuation only for those values (`misa_bind_returns`). -/

namespace Airbender.Reference.Sail
open Reference.RiscV.Sail _root_.Sail.ArchSem

/-- A `SailME` computation with its early return (`.error`) as a value. -/
def runE {α β : Type} : SailRV32.SailME α β → SailRV32.SailM (Except α β)
  | .pure v => pure (.ok v)
  | .impure (.error ret) _ => pure (.error ret)
  | .impure (.ok eff) cont => .impure eff (fun v => runE (cont v))

/-- `MisaOnly` of a `SailME` computation: of its `runE`. -/
def MisaOnlyE {α β : Type} (m : SailRV32.SailME α β) : Prop := MisaOnly (runE m)

theorem runE_bind {α β γ : Type} (m : SailRV32.SailME α β) (k : β → SailRV32.SailME α γ) :
    runE (m >>= k) = runE m >>= fun r => match r with
      | .error ret => pure (.error ret)
      | .ok v => runE (k v) := by
  induction m with
  | pure v => rfl
  | impure eff cont ih =>
    cases eff with
    | error ret => rfl
    | ok eff =>
      show FreeM.impure eff (fun v => runE (FreeM.bind (cont v) k)) = FreeM.bind (FreeM.impure eff _) _
      simp only [FreeM.bind]
      congr 1
      funext v
      exact ih v

/-- `SailME.run` is `runE` with the early return as the result. -/
theorem sailme_run_eq {α : Type} (m : SailRV32.SailME α α) :
    SailRV32.SailME.run m = runE m >>= fun r => pure (match r with | .ok v => v | .error v => v) := by
  induction m with
  | pure v => rfl
  | impure eff cont ih =>
    cases eff with
    | error ret => rfl
    | ok eff =>
      show FreeM.impure eff (fun v => SailRV32.SailME.run (cont v)) = FreeM.bind (FreeM.impure eff _) _
      simp only [FreeM.bind]
      congr 1
      funext v
      exact ih v

theorem misa_sailme_run {α : Type} (m : SailRV32.SailME α α) (h : MisaOnlyE m) :
    MisaOnly (SailRV32.SailME.run m) := by
  rw [sailme_run_eq]
  exact misa_bind _ _ h (fun _ => misa_pure _)

theorem misaE_pure {α β : Type} (v : β) : MisaOnlyE (pure v : SailRV32.SailME α β) := misa_pure _

theorem misaE_throw {α β : Type} (e : α) : MisaOnlyE (SailRV32.SailME.throw e : SailRV32.SailME α β) :=
  misa_pure _

theorem misaE_ite {α β : Type} (c : Prop) [Decidable c] (yes no : SailRV32.SailME α β)
    (hy : MisaOnlyE yes) (hn : MisaOnlyE no) : MisaOnlyE (if c then yes else no) := by
  by_cases h : c
  · simpa only [if_pos h] using hy
  · simpa only [if_neg h] using hn

theorem misaE_bind {α β γ : Type} (m : SailRV32.SailME α β) (k : β → SailRV32.SailME α γ)
    (hm : MisaOnlyE m) (hk : ∀ v, MisaOnlyE (k v)) : MisaOnlyE (m >>= k) := by
  unfold MisaOnlyE
  rw [runE_bind]
  refine misa_bind _ _ hm (fun r => ?_)
  cases r with
  | error ret => exact misa_pure _
  | ok v => exact hk v

/-- A lifted `SailM` action returns its value. -/
theorem runE_lift {α β : Type} (m : SailRV32.SailM β) :
    runE (liftM m : SailRV32.SailME α β) = m >>= fun v => pure (.ok v) := by
  induction m with
  | pure v => rfl
  | impure eff cont ih =>
    show FreeM.impure eff (fun v => runE _) = FreeM.bind (FreeM.impure eff _) _
    simp only [FreeM.bind]
    congr 1
    funext v
    exact ih v

theorem misaE_lift {α β : Type} (m : SailRV32.SailM β) (h : MisaOnly m) :
    MisaOnlyE (liftM m : SailRV32.SailME α β) := by
  unfold MisaOnlyE
  rw [runE_lift]
  exact misa_bind _ _ h (fun _ => misa_pure _)

/-- A bind whose first action returns only values satisfying `property` needs its continuation only for
    those values (the continuation of the other values is never run). -/
theorem misa_bind_returns {α β : Type} (action : SailRV32.SailM α) (next : α → SailRV32.SailM β)
    (property : α → Prop) (first : MisaOnly action) (values : Returns property action)
    (rest : ∀ value, property value → MisaOnly (next value)) : MisaOnly (action >>= next) := by
  unfold MisaOnly at first rest ⊢
  unfold Returns at values
  intro before value after executed
  cases initial : run action before with
  | error error middle =>
    rw [run_bind_of_error _ _ _ _ _ initial] at executed
    cases executed
  | ok input middle =>
    obtain ⟨unchanged, replay⟩ := first before input middle initial
    have holds := values before input middle initial
    subst middle
    rw [run_bind_of_ok _ _ _ _ _ initial] at executed
    obtain ⟨unchanged, finish⟩ := rest input holds before value after executed
    subst after
    refine ⟨rfl, fun state same => ?_⟩
    rw [run_bind_of_ok _ _ _ _ _ (replay state same)]
    exact finish state same

/-- The same through the early-return layer, for a lifted first action. -/
theorem misaE_lift_bind_returns {α β γ : Type} (action : SailRV32.SailM β)
    (next : β → SailRV32.SailME α γ) (property : β → Prop) (first : MisaOnly action)
    (values : Returns property action) (rest : ∀ value, property value → MisaOnlyE (next value)) :
    MisaOnlyE ((liftM action : SailRV32.SailME α β) >>= next) := by
  unfold MisaOnlyE
  rw [runE_bind, runE_lift, freeM_bind_assoc]
  refine misa_bind_returns _ _ property first values (fun v hv => ?_)
  exact rest v hv

end Airbender.Reference.Sail
