import Slop.Sail.Airbender
import Slop.Sail.Contract
import Human.Spec

/-! Simp lemmas describing how `Human.runSail` interprets the basic `SailM` operations. -/

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

@[simp] theorem runF_pure {α : Type} (a : α) (s : SailState) :
    runSail (pure a : SailM α) s = .ok a s := by
  unfold runSail
  rfl

/--  unfolded: the interpreter is the same lambda, here written out once. -/
theorem runF_def {α : Type} (m : SailM α) (s : SailState) :
    runSail m s = (FreeM.liftM (fun
        | .inl (.error err) => throw err
        | .inl (.ok eff) => applyEffect eff
        | .inr (n : Nat) => if h : 0 < n then pure (⟨0, h⟩ : Fin n) else throw Error.Unreachable) m : SailStateM α).run s :=
  rfl

theorem runF_bind_ok {α β : Type} (m : SailM α) (f : α → SailM β) (s s' : SailState) (a : α)
    (h : runSail m s = .ok a s') : runSail (m >>= f) s = runSail (f a) s' := by
  simp only [runF_def] at h ⊢
  rw [show (m >>= f) = FreeM.bind m f from rfl, liftM_bind_run, h]

theorem runF_bind_error {α β : Type} (m : SailM α) (f : α → SailM β) (s s' : SailState)
    (e : Sail.Error exception) (h : runSail m s = .error e s') : runSail (m >>= f) s = .error e s' := by
  simp only [runF_def] at h ⊢
  rw [show (m >>= f) = FreeM.bind m f from rfl, liftM_bind_run, h]

@[simp] theorem runF_bind {α β : Type} (m : SailM α) (f : α → SailM β) (s : SailState) :
    runSail (m >>= f) s = match runSail m s with
      | .ok a s' => runSail (f a) s'
      | .error e s' => .error e s' := by
  cases h : runSail m s with
  | ok a s' => rw [runF_bind_ok m f s s' a h]
  | error e s' => rw [runF_bind_error m f s s' e h]

@[simp] theorem runF_readReg (r : Register) (s : SailState) :
    runSail (readReg r) s = .ok (s.regs r) s := by
  unfold runSail
  rfl

@[simp] theorem runF_writeReg (r : Register) (v : RegisterType r) (s : SailState) :
    runSail (writeReg r v) s =
      .ok () (s.set r v) := by
  unfold runSail
  rfl

@[simp] theorem runF_throw {α : Type} (e : Sail.Error exception) (s : SailState) :
    runSail (throw e : SailM α) s = .error e s := by
  unfold runSail
  rfl

end Slop
