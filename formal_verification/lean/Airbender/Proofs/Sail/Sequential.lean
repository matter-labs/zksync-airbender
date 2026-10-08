import Airbender.Review.Sail

namespace Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- Sail's free monad currently exposes no lawful-monad instance. These sequencing
    lemmas are proved once over its existing definition and reused by instruction proofs. -/
theorem freeM_bind_assoc {Eff α β γ : Type} [Effect Eff]
    (program : FreeM Eff α) (next : α → FreeM Eff β) (last : β → FreeM Eff γ) :
    ((program >>= next) >>= last) = (program >>= fun value => next value >>= last) := by
  induction program with
  | pure value => rfl
  | impure effect cont ih =>
    change FreeM.impure effect (fun value => FreeM.bind (FreeM.bind (cont value) next) last) =
      FreeM.impure effect (fun value => FreeM.bind (cont value) (fun value => FreeM.bind (next value) last))
    congr 1
    funext value
    exact ih value

theorem freeM_pure_bind {Eff α β : Type} [Effect Eff] (value : α)
    (next : α → FreeM Eff β) : ((pure value : FreeM Eff α) >>= next) = next value := rfl

theorem liftM_bind {Eff α β : Type} [Effect Eff] {m : Type → Type}
    [Monad m] [LawfulMonad m] (interpret : (effect : Eff) → m (Effect.ret effect))
    (program : FreeM Eff α) (next : α → FreeM Eff β) :
    FreeM.liftM interpret (FreeM.bind program next) =
      (FreeM.liftM interpret program >>= fun value => FreeM.liftM interpret (next value)) := by
  induction program with
  | pure value => simp [FreeM.bind, FreeM.liftM]
  | impure effect cont ih => simp [FreeM.bind, FreeM.liftM, ih, bind_assoc]

variable [Arch]

/-- Eliminating Sail's early-return layer preserves an embedded native effect
    and its continuation. This is about the existing free monads, not a new runtime. -/
theorem early_return_lift_bind {ε α β : Type} (program : PreSailM ε α)
    (next : α → PreSailME ε β β) :
    PreSail.PreSailME.run (liftM program >>= next) =
      (program >>= fun value => PreSail.PreSailME.run (next value)) := by
  induction program with
  | pure value => rfl
  | impure effect cont ih =>
    change FreeM.impure effect (fun value =>
      PreSail.PreSailME.run (liftM (cont value) >>= next)) =
      FreeM.impure effect (fun value => cont value >>= fun result =>
        PreSail.PreSailME.run (next result))
    congr 1
    funext value
    exact ih value

/-- Sequential interpretation preserves the generated model's monadic sequencing. -/
theorem interpret_bind {ε α β : Type} (program : PreSailM ε α)
    (next : α → PreSailM ε β) :
    interpretSailEffects (program >>= next) =
      (interpretSailEffects program >>= fun value => interpretSailEffects (next value)) := by
  exact liftM_bind _ program next

/-- Shared rule for discharging an external read contract before continuing execution. -/
theorem run_bind_of_ok {ε α β : Type} (program : PreSailM ε α)
    (next : α → PreSailM ε β) (state state' : SequentialState Arch.register_type)
    (value : α) (h : run program state = .ok value state') :
    run (program >>= next) state = run (next value) state' := by
  unfold run at *
  rw [interpret_bind]
  change EStateM.bind (interpretSailEffects program)
    (fun value => interpretSailEffects (next value)) state = _
  change interpretSailEffects program state = .ok value state' at h
  simp only [EStateM.bind, h]
  rfl

/-- A failed native effect stops the original continuation. Used when checking
    that missing public configuration is rejected rather than silently supplied. -/
theorem run_bind_of_error {ε α β : Type} (program : PreSailM ε α)
    (next : α → PreSailM ε β) (state state' : SequentialState Arch.register_type)
    (error : _root_.Sail.Error ε) (h : run program state = .error error state') :
    run (program >>= next) state = .error error state' := by
  unfold run at *
  rw [interpret_bind]
  change EStateM.bind (interpretSailEffects program)
    (fun value => interpretSailEffects (next value)) state = _
  change interpretSailEffects program state = .error error state' at h
  simp only [EStateM.bind, h]

end Airbender.Reference.Sail
