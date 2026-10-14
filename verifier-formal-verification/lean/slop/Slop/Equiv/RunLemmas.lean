import Slop.Equiv.Jump

/-! Lemmas for running Sail code symbolically on an Airbender state: anything the oracle evaluates (fixed
registers only) holds on every `Configured` state; register reads/writes; `SailME` peeled. Used for the memory path
(loads, stores, fetch). -/

open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

/-- Any Sail computation that the oracle evaluates (fixed registers only): the same result on every Airbender
state, state unchanged. -/
theorem oracle_run {α : Type} {σ : SailState} (hs : Airbender.Configured σ) (m : SailM α) (a : α)
    (h : runOracle knownDemo (fun _ => none) m = some a) : runSail m σ = .ok a σ :=
  runOracle_sound knownDemo (fun _ => none) σ h (known_sys hs) (fun _ _ h => by simp at h)

theorem run_readReg_bind {β : Type} (r : Register) (f : RegisterType r → SailM β) (σ : SailState) {res}
    (h : runSail (f (σ.regs r)) σ = res) : runSail (readReg r >>= f) σ = res := by
  rw [Slop.runF_bind, Slop.runF_readReg]; exact h

theorem run_writeReg_bind {β : Type} (r : Register) (v : RegisterType r) (f : Unit → SailM β) (σ : SailState) {res}
    (h : runSail (f ()) (σ.set r v) = res) : runSail (writeReg r v >>= f) σ = res := by
  rw [Slop.runF_bind, Slop.runF_writeReg]; exact h

theorem sys_set {σ : SailState} (hs : Airbender.Configured σ) (r : Register) (v : RegisterType r)
    (hr : Airbender.Volatile r = true) : Airbender.Configured (σ.set r v) := by
  intro r' hr'
  have hne : r ≠ r' := by intro h; subst h; simp_all
  simp only [SailState.set, hne, dite_false]
  exact hs r' hr'

theorem me_run_pure_bind {α β : Type} (a : α) (f : α → SailME β β) :
    PreSail.PreSailME.run (pure a >>= f) = PreSail.PreSailME.run (f a) := rfl

theorem me_run_throw_bind {α β : Type} (e : β) (f : α → SailME β β) :
    PreSail.PreSailME.run (SailME.throw e >>= f) = pure e := rfl

theorem me_bind_assoc {α β γ : Type} (m : SailME γ α) (f : α → SailME γ β) (g : β → SailME γ γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  induction m with
  | pure a => rfl
  | impure eff cont ih =>
    show FreeM.impure _ _ = FreeM.impure _ _
    congr 1; funext v; exact ih v

theorem me_run_bind_assoc {α β γ : Type} (m : SailME γ α) (f : α → SailME γ β) (g : β → SailME γ γ) :
    PreSail.PreSailME.run ((m >>= f) >>= g) = PreSail.PreSailME.run (m >>= fun x => f x >>= g) := by
  rw [me_bind_assoc]

end Slop.Equiv
