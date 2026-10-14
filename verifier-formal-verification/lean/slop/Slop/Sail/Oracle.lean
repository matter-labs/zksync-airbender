import Slop.Sail.Config
import Slop.Sail.Contract
import Human.Spec
import Slop.Sail.Monad

/-! Oracle interpreter: resolve a `SailM` computation whose register and memory inputs are known,
without unfolding symbolically. Answers mirror `Human.applyEffect`; any write, unknown read or error
stops the oracle. Recursion is structural on a fuel counter (one unit per effect). -/

open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Slop

/-- `n` bytes at `addr` if every one is known; mirrors `Human.readBytes`. -/
def knownBytes (km : Nat → Option (BitVec 8)) (addr : Nat) : (n : Nat) → Option (BitVec (8 * n))
  | 0 => some 0#0
  | n+1 => match knownBytes km (addr+1) n, km addr with
    | some r, some b => some ((by omega : 8 * n + 8 = 8 * (n + 1)) ▸ (r.append b))
    | _, _ => none

/-- The value of an effect when the oracle answers it without writing; `none` otherwise. -/
def oracleEff (known : (r : Register) → Option (RegisterType r)) (knownMem : Nat → Option (BitVec 8)) :
    (eff : InstructionEffect) → Option (InstructionEffect.ret eff)
  | .regRead reg _ => known reg
  | .regWrite .. => none
  | .memRead req => (knownBytes knownMem req.address.toNat req.size).map fun v => .ok (v, 0#req.numTag)
  | .memWrite .. => none
  | .getCycleCount => some (0 : Nat)
  | .barrier _ | .cacheOp _ | .tlbOp _ | .translationStart _ | .translationEnd _ | .archException _
  | .returnException | .memWriteAnnounce _ | .printMessage _ | .clockCycle => some ()

/-- Oracle run with `n` effects of fuel. Resolves choices to index 0 exactly as `runSail` does. -/
def oracleGo {α : Type} (known : (r : Register) → Option (RegisterType r))
    (knownMem : Nat → Option (BitVec 8)) : Nat → SailM α → Option α
  | 0, _ => none
  | _ + 1, .pure a => some a
  | _ + 1, .impure (.inl (.error _)) _ => none
  | n + 1, .impure (.inl (.ok eff)) cont =>
      (oracleEff known knownMem eff).bind fun v => oracleGo known knownMem n (cont v)
  | n + 1, .impure (.inr k) cont =>
      @dite _ (@LT.lt Nat instLTNat 0 k) (Nat.decLt 0 k)
        (fun h => oracleGo known knownMem n (cont (⟨0, h⟩ : Fin k))) (fun _ => none)

/-- Fuel bound: far more effects than any fetch/decode of one instruction performs. -/
def oracleFuel : Nat := 1000

/-- The oracle: `some a` means `m` returns `a` and leaves the state unchanged, for every state that
agrees with `known` and `knownMem`. -/
def runOracle {α : Type} (known : (r : Register) → Option (RegisterType r))
    (knownMem : Nat → Option (BitVec 8)) (m : SailM α) : Option α :=
  oracleGo known knownMem oracleFuel m

/-! Soundness -/

theorem knownBytes_sound (km : Nat → Option (BitVec 8)) (mem : Nat → BitVec 8)
    (hm : ∀ i b, km i = some b → mem i = b) :
    ∀ (n addr : Nat) (v : BitVec (8 * n)), knownBytes km addr n = some v → readBytes mem addr n = v := by
  intro n
  induction n with
  | zero => intro addr v h; simp only [knownBytes] at h; cases h; rfl
  | succ n ih =>
    intro addr v h
    simp only [knownBytes] at h
    split at h
    · rename_i r b hr hb
      cases h
      have h1 := ih (addr+1) r hr
      have h2 := hm addr b hb
      subst h1; subst h2
      rfl
    · simp at h

theorem oracleEff_sound (known : (r : Register) → Option (RegisterType r))
    (km : Nat → Option (BitVec 8)) (s : SailState)
    (hk : ∀ r v, known r = some v → s.regs r = v) (hm : ∀ i b, km i = some b → s.mem i = b)
    (eff : InstructionEffect) (v : InstructionEffect.ret eff)
    (h : oracleEff known km eff = some v) : applyEffect eff s = .ok v s := by
  cases eff with
  | regRead reg acc =>
    simp only [oracleEff] at h
    have e : s.regs reg = v := hk reg v h
    show EStateM.Result.ok (s.regs reg) s = EStateM.Result.ok v s
    rw [e]
    rfl
  | regWrite => simp [oracleEff] at h
  | memRead req =>
    simp only [oracleEff] at h
    cases hb : knownBytes km req.address.toNat req.size with
    | none => rw [hb] at h; cases h
    | some w =>
      rw [hb] at h
      change some (Except.ok (w, 0#req.numTag)) = some v at h
      cases h
      show EStateM.Result.ok (Except.ok (readBytes s.mem req.address.toNat req.size, 0#req.numTag)) s
        = EStateM.Result.ok (Except.ok (w, 0#req.numTag)) s
      rw [knownBytes_sound km s.mem hm _ _ _ hb] <;> rfl
  | memWrite => simp [oracleEff] at h
  | getCycleCount => simp only [oracleEff] at h; cases h; rfl
  | barrier _ | cacheOp _ | tlbOp _ | translationStart _ | translationEnd _ | archException _
  | returnException | memWriteAnnounce _ | printMessage _ | clockCycle =>
    simp only [oracleEff] at h; cases h; rfl

theorem liftM_impure_ok {ε σ α Eff : Type} [Effect Eff] (I : (e : Eff) → EStateM ε σ (Effect.ret e))
    (e : Eff) (cont : Effect.ret e → FreeM Eff α) (s : σ) (v : Effect.ret e) (h : I e s = .ok v s) :
    (FreeM.liftM I (FreeM.impure e cont)).run s = (FreeM.liftM I (cont v)).run s := by
  show EStateM.bind (I e) (fun res => FreeM.liftM I (cont res)) s = _
  simp only [EStateM.bind, h]
  rfl

theorem runF_impure_ok {α : Type} (eff : InstructionEffect)
    (cont : InstructionEffect.ret eff → FreeM ((Except (Sail.Error exception) InstructionEffect) ⊕ FinChoice) α)
    (s : SailState) (v : InstructionEffect.ret eff) (h : applyEffect eff s = .ok v s) :
    runSail (FreeM.impure (.inl (.ok eff)) cont) s = runSail (cont v) s := by
  rw [runF_def, runF_def]
  exact liftM_impure_ok _ (Sum.inl (Except.ok eff) : (Except (Sail.Error exception) InstructionEffect) ⊕ FinChoice) cont s v h

theorem runF_choice_pos {α : Type} (k : FinChoice) (hk0 : @LT.lt Nat instLTNat 0 k)
    (cont : Fin k → FreeM ((Except (Sail.Error exception) InstructionEffect) ⊕ FinChoice) α) (s : SailState) :
    runSail (FreeM.impure (.inr k) cont) s = runSail (cont (⟨0, hk0⟩ : Fin k)) s := by
  rw [runF_def, runF_def]
  exact liftM_impure_ok _ (Sum.inr k : (Except (Sail.Error exception) InstructionEffect) ⊕ FinChoice) cont s ⟨0, hk0⟩ (by simp [hk0] <;> rfl)

theorem oracleGo_sound {α : Type} (known : (r : Register) → Option (RegisterType r))
    (km : Nat → Option (BitVec 8)) (s : SailState)
    (hk : ∀ r v, known r = some v → s.regs r = v) (hm : ∀ i b, km i = some b → s.mem i = b) :
    ∀ (n : Nat) (m : SailM α) (a : α), oracleGo known km n m = some a → runSail m s = .ok a s := by
  intro n
  induction n with
  | zero => intro m a h; simp [oracleGo] at h
  | succ n ih =>
    intro m a h
    match m with
    | .pure x =>
      simp [oracleGo] at h
      subst h
      exact runF_pure _ s
    | .impure (.inl (.error e)) cont => simp [oracleGo] at h
    | .impure (.inl (.ok eff)) cont =>
      simp only [oracleGo] at h
      cases hv : oracleEff known km eff with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_some] at h
        rw [runF_impure_ok eff cont s v (oracleEff_sound known km s hk hm eff v hv)]
        exact ih _ _ h
    | .impure (.inr k) cont =>
      simp only [oracleGo] at h
      by_cases hk0 : @LT.lt Nat instLTNat 0 k
      · rw [dif_pos hk0] at h
        rw [runF_choice_pos k hk0 cont s]
        exact ih _ _ h
      · rw [dif_neg hk0] at h
        simp at h

theorem runOracle_sound {α : Type} (known : (r : Register) → Option (RegisterType r))
    (km : Nat → Option (BitVec 8)) (s : SailState) {m : SailM α} {a : α}
    (h : runOracle known km m = some a)
    (hk : ∀ r v, known r = some v → s.regs r = v) (hm : ∀ i b, km i = some b → s.mem i = b) :
    runSail m s = .ok a s :=
  oracleGo_sound known km s hk hm _ m a h

/-! Demo: `addi a0, a0, 1` (word 0x00150513) with known non-volatile registers from `resetState`. -/

noncomputable def knownDemo : (r : Register) → Option (RegisterType r) :=
  fun r => if Volatile r then none else some (resetState.regs r)

/-- Bool test for `ADDI rd=a0, rs1=a0, imm=1` (`instruction` has no `DecidableEq`). -/
def isAddi : instruction → Bool
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI) =>
      decide (imm = 1#12) && decide (rs1 = (10#5 : BitVec 5)) && decide (rd = (10#5 : BitVec 5))
  | _ => false

theorem isAddi_eq {i : instruction} (h : isAddi i = true) :
    i = .ITYPE (1#12, .Regidx 10#5, .Regidx 10#5, .ADDI) := by
  cases i with
  | ITYPE p =>
    obtain ⟨imm, ⟨rs1⟩, ⟨rd⟩, op⟩ := p
    cases op <;> simp only [isAddi, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    subst h1; subst h2; subst h3; rfl
  | _ => simp [isAddi] at h

theorem demo_bool :
    (runOracle knownDemo (fun _ => none) (ext_decode 0x00150513#32)).map isAddi = some true := by
  decide +kernel

theorem demo :
    runOracle knownDemo (fun _ => none) (ext_decode 0x00150513#32)
      = some (.ITYPE (1#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by
  have hb := demo_bool
  revert hb
  cases runOracle knownDemo (fun _ => none) (ext_decode 0x00150513#32) with
  | none => intro hb; simp at hb
  | some i =>
    intro hb
    simp only [Option.map_some, Option.some.injEq] at hb
    rw [isAddi_eq hb]

theorem demo_runF (s : SailState) (hs : Configured s) :
    runSail (ext_decode 0x00150513#32) s = .ok (.ITYPE (1#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) s := by
  refine runOracle_sound knownDemo (fun _ => none) s demo ?_ ?_
  · intro r v h
    unfold knownDemo at h
    split at h
    · simp at h
    · rename_i hv
      cases h
      exact hs r (by simpa using hv)
  · intro i b h; simp at h

end Slop
