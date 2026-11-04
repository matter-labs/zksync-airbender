import Slop.Sail.Sequential
import Human.Helpers.Core.Configuration

/-! # Forward simulation: lean-sail's sequential interpreter to `Configuration.runSail`

A lean-sail state `st` (hash maps) and a `SailState` `σ` agree when `σ` reads every register and byte as `st` does,
with the defaults `runSail` uses for entries `st` does not hold. Clock effects are excluded (`ClockFree`): the
generated model never emits them, and the two interpreters differ on them (lean-sail counts cycles, `runSail` gives 0).
A successful lean-sail run then succeeds under `runSail` with agreeing final states. -/

namespace Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem Configuration Airbender.Reference.Sail

/-- The instruction effects the forward simulation covers. -/
def InstrCovered : InstructionEffect → Prop
  | .clockCycle => False
  | .getCycleCount => False
  | .memRead _ => False
  | .memWrite _ _ _ => False
  | _ => True

/-- Effects the forward simulation covers: the generated model's register, control and no-op effects. Clock and
cycle-count effects are excluded (the two interpreters differ on them); memory effects are not yet covered. -/
def Covered {ue : Type} : (Except (Sail.Error ue) InstructionEffect ⊕ FinChoice) → Prop
  | .inl (.ok eff) => InstrCovered eff
  | _ => True

/-- A computation whose every effect is covered. -/
inductive Simple {ue α : Type} : PreSailM ue α → Prop
  | pure (a : α) : Simple (FreeM.pure a)
  | impure (e) (k : Effect.ret e → PreSailM ue α) : Covered e → (∀ x, Simple (k x)) → Simple (FreeM.impure e k)

/-- A lean-sail state and a `SailState` agree on every register and byte. -/
def Agrees (st : State) (σ : SailState) : Prop :=
  (∀ r, σ.regs r = (st.regs.get? r).getD (resetState.regs r)) ∧ (∀ a, σ.mem a = (st.mem.get? a).getD 0)


theorem agrees_reg_read {st : State} {σ : SailState} (h : Agrees st σ) {r : SailRV32.Register} {v : SailRV32.RegisterType r}
    (hv : st.regs.get? r = some v) : σ.regs r = v := by
  rw [h.1 r, hv]; rfl

theorem agrees_reg_write {st : State} {σ : SailState} (h : Agrees st σ) (r : SailRV32.Register)
    (v : SailRV32.RegisterType r) :
    Agrees { st with regs := st.regs.insert r v } (σ.set r v) := by
  constructor
  · intro r'
    by_cases hr : r = r'
    · subst hr
      simp [SailState.set, Std.ExtDHashMap.get?_insert]
    · simp [SailState.set, hr, Std.ExtDHashMap.get?_insert, Ne.symm hr, h.1 r']
  · intro a
    simp [SailState.set, h.2 a]


/-- A byte read by lean-sail succeeds only if the byte is held; then it is the byte `σm` gives. -/
theorem lean_readByte_eq (σm : Nat → BitVec 8) (st : State) (hm : ∀ a, σm a = (st.mem.get? a).getD 0)
    (addr : Nat) (b : BitVec 8) (st' : State)
    (h : (Sail.ArchSem.readByte addr : ArchSemSeqM Unit (BitVec 8)).run st = .ok b st') :
    b = σm addr ∧ st' = st := by
  unfold Sail.ArchSem.readByte at h
  simp only [EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get] at h
  cases hg : st.mem.get? addr with
  | none =>
    rw [hg] at h
    simp only [throwThe, MonadExceptOf.throw, EStateM.throw, reduceCtorEq] at h
    cases h
  | some x =>
    rw [hg] at h
    simp only [pure, EStateM.pure, EStateM.Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [hm, hg]; rfl, rfl⟩

/-- Appending the empty word to a byte gives the byte (`readBytes` builds words this way). -/
theorem zero_append_byte (x : BitVec 8) : (BitVec.append (0#(8 * 0)) x) = x := by
  show (0#0 ++ x : BitVec 8) = x
  rw [BitVec.zero_width_append]; simp

/-- A successful bind: the first action succeeded, then the continuation. -/
theorem bind_run_ok {ue α β : Type} (x : ArchSemSeqM ue α) (f : α → ArchSemSeqM ue β) (s : State)
    {v : β} {s' : State} (h : (x >>= f).run s = .ok v s') :
    ∃ a s1, x.run s = .ok a s1 ∧ (f a).run s1 = .ok v s' := by
  unfold EStateM.run at h ⊢
  change EStateM.bind x f s = _ at h
  unfold EStateM.bind at h
  split at h
  · rename_i a s1 hx
    exact ⟨a, s1, hx, h⟩
  · cases h

theorem lean_readBytes_eq (σm : Nat → BitVec 8) (st : State) (hm : ∀ a, σm a = (st.mem.get? a).getD 0) (n : Nat) :
    ∀ (addr : Nat) (v : BitVec (8 * n)) (st' : State),
      (Sail.ArchSem.readBytes n addr : ArchSemSeqM Unit (BitVec (8 * n))).run st = .ok v st' →
      v = Configuration.readBytes σm addr n := by
  induction n with
  | zero => intro addr v st' h; simp only [Sail.ArchSem.readBytes] at h; cases h; rfl
  | succ n ih =>
    intro addr v st' h
    cases n with
    | zero =>
      unfold Sail.ArchSem.readBytes at h
      obtain ⟨b, s1, hb, hp⟩ := bind_run_ok _ _ _ h
      obtain ⟨hbv, hs1⟩ := lean_readByte_eq σm st hm addr b s1 hb
      subst hs1
      change EStateM.Result.ok _ _ = _ at hp
      cases hp
      rw [hbv]
      apply BitVec.eq_of_toNat_eq
      simp only [Configuration.readBytes]
      exact congrArg BitVec.toNat (zero_append_byte (σm addr)).symm
    | succ n =>
      simp only [Sail.ArchSem.readBytes] at h
      obtain ⟨b, s1, hb, hp⟩ := bind_run_ok _ _ _ h
      obtain ⟨hbv, hs1⟩ := lean_readByte_eq σm st hm addr b s1 hb
      subst hs1
      obtain ⟨bytes, s2, hr, hq⟩ := bind_run_ok _ _ _ hp
      have hbytes := ih (addr + 1) bytes s2 hr
      change EStateM.Result.ok _ _ = _ at hq
      cases hq
      rw [hbytes, hbv]
      rfl


/-- A state change that leaves the registers and the memory alone agrees with the same `SailState`. -/
theorem agrees_of_same {st st1 : State} {σ : SailState} (h : Agrees st σ) (hr : st1.regs = st.regs)
    (hm : st1.mem = st.mem) : Agrees st1 σ := by
  refine ⟨fun r => ?_, fun a => ?_⟩
  · rw [h.1 r, hr]
  · rw [h.2 a, hm]

/-- One covered instruction effect: runSail's result and state agree with lean-sail's. -/
theorem effect_sim {ue : Type} (eff : InstructionEffect) (st st1 : State) (σ : SailState) (r : eff.ret)
    (h : Agrees st σ)
    (hc : InstrCovered eff)
    (run : (interpretInstructionEffect eff : ArchSemSeqM ue eff.ret).run st = .ok r st1) :
    ∃ σ1, (applyEffect eff : SailStateM eff.ret).run σ = .ok r σ1 ∧ Agrees st1 σ1 := by
  cases eff with
  | regRead reg acc =>
    simp only [interpretInstructionEffect, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
      EStateM.get, pure] at run
    cases hx : st.regs.get? reg with
    | none =>
      rw [hx] at run
      simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at run
    | some x =>
      rw [hx] at run
      simp only [EStateM.Result.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨σ, ?_, h⟩
      simp only [applyEffect, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
        EStateM.run]
      rw [agrees_reg_read h hx]
  | regWrite reg acc v =>
    simp only [interpretInstructionEffect, EStateM.run, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet, Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    refine ⟨σ.set reg v, ?_, agrees_reg_write h reg v⟩
    simp only [applyEffect, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.run]
    rfl
  | barrier b =>
    simp only [interpretInstructionEffect, EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq,
      Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩
  | memRead req => exact absurd hc (by simp [InstrCovered])
  | memWrite req v t => exact absurd hc (by simp [InstrCovered])
  | clockCycle => exact absurd hc (by simp [InstrCovered])
  | getCycleCount => exact absurd hc (by simp [InstrCovered])
  | cacheOp op =>
    simp only [interpretInstructionEffect, EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq,
      Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩
  | tlbOp op =>
    simp only [interpretInstructionEffect, EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq,
      Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩
  | translationStart t =>
    simp only [interpretInstructionEffect, EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq,
      Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩
  | translationEnd t =>
    simp only [interpretInstructionEffect, EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq,
      Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩
  | archException e =>
    simp only [interpretInstructionEffect, EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq,
      Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩
  | returnException =>
    simp only [interpretInstructionEffect, EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq,
      Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩
  | memWriteAnnounce req =>
    simp only [interpretInstructionEffect, EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq,
      Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩
  | printMessage msg =>
    simp only [interpretInstructionEffect, EStateM.run, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet, EStateM.Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨σ, by simp [applyEffect, EStateM.run, pure, EStateM.pure], h⟩

/-- Introduce a successful bind from its two successful halves. -/
theorem bind_run_intro {ε σ α β : Type} (x : EStateM ε σ α) (g : α → EStateM ε σ β) {s : σ} {a : α} {s1 : σ}
    {v : β} {s' : σ} (hx : x.run s = .ok a s1) (hg : (g a).run s1 = .ok v s') :
    (x >>= g).run s = .ok v s' := by
  unfold EStateM.run at *
  change EStateM.bind x g s = _
  unfold EStateM.bind
  rw [hx]
  exact hg

/-- Lean-sail's sequential interpreter, for covered computations, against `runSail`. -/
theorem forward_simple {α : Type} (m : SailRV32.SailM α) :
    ∀ (st st' : State) (σ : SailState) (v : α), Simple m → Agrees st σ →
      (interpretSailEffects m).run st = .ok v st' → ∃ σ', runSail m σ = .ok v σ' ∧ Agrees st' σ' := by
  induction m with
  | pure a =>
    intro st st' σ v _ h hrun
    change EStateM.Result.ok a st = _ at hrun
    cases hrun
    exact ⟨σ, rfl, h⟩
  | impure e k ih =>
    intro st st' σ v hs h hrun
    cases hs with
    | impure _ _ hc hk =>
      cases e with
      | inl r =>
        cases r with
        | error err =>
          unfold interpretSailEffects FreeM.liftM at hrun
          unfold EStateM.run at hrun
          change EStateM.bind (EStateM.throw err) _ st = _ at hrun
          simp only [EStateM.bind, EStateM.throw] at hrun
          cases hrun
        | ok eff =>
          change (interpretInstructionEffect eff >>= fun res => FreeM.liftM _ (k res)).run st = _ at hrun
          obtain ⟨res, st1, hx, hk'⟩ := bind_run_ok _ _ _ hrun
          obtain ⟨σ1, hσ, hA⟩ := effect_sim eff st st1 σ res h hc hx
          obtain ⟨σ', hσ', hA'⟩ := ih res st1 st' σ1 v (hk res) hA hk'
          refine ⟨σ', ?_, hA'⟩
          unfold runSail at hσ' ⊢
          exact bind_run_intro _ _ hσ hσ'
      | inr n =>
        unfold interpretSailEffects FreeM.liftM at hrun
        dsimp only at hrun
        by_cases hn : (0 : Nat) < n
        · rw [dif_pos hn] at hrun
          obtain ⟨res, st1, hx, hk'⟩ := bind_run_ok _ _ _ hrun
          change EStateM.Result.ok _ _ = _ at hx
          cases hx
          obtain ⟨σ', hσ', hA'⟩ := ih _ st st' σ v (hk _) h hk'
          refine ⟨σ', ?_, hA'⟩
          unfold runSail at hσ' ⊢
          exact bind_run_intro _ _ (by simp only [dif_pos hn]; rfl) hσ'
        · rw [dif_neg hn] at hrun
          unfold EStateM.run at hrun
          change EStateM.bind (EStateM.throw _) _ st = _ at hrun
          simp only [EStateM.bind, EStateM.throw] at hrun
          cases hrun
end Airbender.Reference.RiscV.Sail
