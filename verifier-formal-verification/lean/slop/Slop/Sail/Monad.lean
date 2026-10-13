import Slop.Sail.Config
import Slop.Sail.Contract
import Human.Spec

/-! Simp lemmas describing how `Human.runF` interprets the basic `SailM` operations. -/

open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Slop

/-- Interpreting a bind of the free monad is sequencing of the interpreter. -/
theorem liftM_bind_run {Eff : Type} [Effect Eff] {ε σ α β : Type}
    (I : (e : Eff) → EStateM ε σ (Effect.ret e)) (x : FreeM Eff α) (f : α → FreeM Eff β) (s : σ) :
    (FreeM.liftM I (FreeM.bind x f)).run s =
      match (FreeM.liftM I x).run s with
      | .ok a s' => (FreeM.liftM I (f a)).run s'
      | .error e s' => .error e s' := by
  induction x generalizing s with
  | pure a => rfl
  | impure c cont ih =>
    change (EStateM.bind (I c) (fun res => FreeM.liftM I ((cont res).bind f))) s =
      match (EStateM.bind (I c) (fun res => FreeM.liftM I (cont res))) s with
      | .ok a s' => (FreeM.liftM I (f a)).run s'
      | .error e s' => .error e s'
    simp only [EStateM.bind]
    cases h : I c s with
    | ok r s' => exact ih r s'
    | error e s' => rfl

@[simp] theorem runF_pure {α : Type} (a : α) (s : FState) :
    runF (pure a : SailM α) s = .ok a s := by
  unfold runF
  rfl

/--  unfolded: the interpreter is the same lambda, here written out once. -/
theorem runF_def {α : Type} (m : SailM α) (s : FState) :
    runF m s = (FreeM.liftM (fun
        | .inl (.error err) => throw err
        | .inl (.ok eff) => interpEff eff
        | .inr (n : Nat) => if h : 0 < n then pure (⟨0, h⟩ : Fin n) else throw Error.Unreachable) m : FM α).run s :=
  rfl

theorem runF_bind_ok {α β : Type} (m : SailM α) (f : α → SailM β) (s s' : FState) (a : α)
    (h : runF m s = .ok a s') : runF (m >>= f) s = runF (f a) s' := by
  simp only [runF_def] at h ⊢
  rw [show (m >>= f) = FreeM.bind m f from rfl, liftM_bind_run, h]

theorem runF_bind_error {α β : Type} (m : SailM α) (f : α → SailM β) (s s' : FState)
    (e : Sail.Error exception) (h : runF m s = .error e s') : runF (m >>= f) s = .error e s' := by
  simp only [runF_def] at h ⊢
  rw [show (m >>= f) = FreeM.bind m f from rfl, liftM_bind_run, h]

@[simp] theorem runF_bind {α β : Type} (m : SailM α) (f : α → SailM β) (s : FState) :
    runF (m >>= f) s = match runF m s with
      | .ok a s' => runF (f a) s'
      | .error e s' => .error e s' := by
  cases h : runF m s with
  | ok a s' => rw [runF_bind_ok m f s s' a h]
  | error e s' => rw [runF_bind_error m f s s' e h]

@[simp] theorem runF_readReg (r : Register) (s : FState) :
    runF (readReg r) s = .ok (s.regs r) s := by
  unfold runF
  rfl

@[simp] theorem runF_writeReg (r : Register) (v : RegisterType r) (s : FState) :
    runF (writeReg r v) s =
      .ok () (s.set r v) := by
  unfold runF
  rfl

@[simp] theorem runF_throw {α : Type} (e : Sail.Error exception) (s : FState) :
    runF (throw e : SailM α) s = .error e s := by
  unfold runF
  rfl

end Slop
