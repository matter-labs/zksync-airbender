import Slop.Sail.Config
import Slop.Sail.Contract
import Human.Spec
import Slop.Sail.Monad
import Slop.Sail.Oracle

/-! Write-tracking oracle. A `Known` map records register values (including values written during the
run), the known image bytes (`code`, answering instruction fetches only) and the total data memory
(`data`, symbolic in proofs). Data reads and writes go through `readBytes` / `writeBytes` at the
requested address, so no address equality is ever decided. Soundness: the interpreter `runF` ends in
a state `s'` that agrees with the final map (`s'.mem = K'.data`) and leaves unknown registers untouched. -/

open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Slop.Wr

structure Known where
  regs : (r : Register) → Option (RegisterType r)
  /-- Known image bytes. Used ONLY for instruction fetches. -/
  code : Nat → Option (BitVec 8)
  /-- Total data memory (in proofs: `s.mem`, symbolic). -/
  data : Nat → BitVec 8
  /-- Registers written so far (most recent first). A register not in `wr` keeps its value. -/
  wr : List Register := []

/-- Record a write of `v` to `r`. -/
def Known.set (K : Known) (r : Register) (v : RegisterType r) : Known :=
  { K with regs := fun r' => if h : r = r' then some (h ▸ v) else K.regs r', wr := r :: K.wr }

/-- Every known fact holds in `s`. -/
def Known.Agrees (K : Known) (s : FState) : Prop :=
  (∀ r v, K.regs r = some v → s.regs r = v) ∧ (∀ i b, K.code i = some b → s.mem i = b) ∧ K.data = s.mem

theorem Known.agrees_set (K : Known) (s : FState) (hK : K.Agrees s) (r : Register) (v : RegisterType r) :
    (K.set r v).Agrees (s.set r v) := by
  refine ⟨fun r' w hw => ?_, fun i b hb => hK.2.1 i b hb, hK.2.2⟩
  · unfold Known.set at hw
    unfold FState.set
    by_cases h : r = r'
    · subst h
      simpa [Known.set, FState.set] using hw
    · simpa [Known.set, FState.set, h] using hK.1 r' w (by simpa [Known.set, h] using hw)

/-- Bytes answering a read: an instruction fetch reads the code image, any other read the data map. -/
def readAnswer (K : Known) (req : MemRequest) : Option (BitVec (8 * req.size)) :=
  if ak_is_ifetch req.accessKind then knownBytes K.code req.address.toNat req.size
  else some (readBytes K.data req.address.toNat req.size)

theorem readAnswer_sound (K : Known) (s : FState) (hK : K.Agrees s) (req : MemRequest)
    (w : BitVec (8 * req.size)) (h : readAnswer K req = some w) :
    w = readBytes s.mem req.address.toNat req.size := by
  unfold readAnswer at h
  split at h
  · exact (knownBytes_sound K.code s.mem hK.2.1 _ _ _ h).symm
  · have hw := Option.some.inj h
    rw [← hw, hK.2.2]

/-- Effect step: the answer, the new map, and the state after the effect.
A store may overwrite image bytes, so it forgets all code facts (sound; no address equality needed). -/
def oracleEff (K : Known) : (eff : InstructionEffect) → Option (InstructionEffect.ret eff × Known)
  | .regRead reg _ => match K.regs reg with
    | some v => some (v, K)
    | none => none
  | .regWrite reg _ v => some ((), K.set reg v)
  | .memRead req => (readAnswer K req).map fun v => (.ok (v, 0#req.numTag), K)
  | .memWrite req v _ => some (.ok (), { K with data := writeBytes K.data req.address.toNat req.size v, code := fun _ => none })
  | .getCycleCount => some ((0 : Nat), K)
  | .barrier _ | .cacheOp _ | .tlbOp _ | .translationStart _ | .translationEnd _ | .archException _
  | .returnException | .memWriteAnnounce _ | .printMessage _ | .clockCycle => some ((), K)

/-- Oracle run with `n` effects of fuel. Choices resolve to index 0, as in `runF`. -/
def oracleGo {α : Type} : Nat → Known → SailM α → Option (α × Known)
  | 0, _, _ => none
  | _ + 1, K, .pure a => some (a, K)
  | _ + 1, _, .impure (.inl (.error _)) _ => none
  | n + 1, K, .impure (.inl (.ok eff)) cont =>
      (oracleEff K eff).bind fun p => oracleGo n p.2 (cont p.1)
  | n + 1, K, .impure (.inr k) cont =>
      @dite _ (@LT.lt Nat instLTNat 0 k) (Nat.decLt 0 k)
        (fun h => oracleGo n K (cont (⟨0, h⟩ : Fin k))) (fun _ => none)

def oracleFuel : Nat := 1000

/-- Oracle with write tracking. `some (a, K')`: `m` returns `a`; `K'` is the map after the run. -/
def runOracleW {α : Type} (K : Known) (m : SailM α) : Option (α × Known) :=
  oracleGo oracleFuel K m

/-! Soundness -/

theorem liftM_impure_gen {ε σ α Eff : Type} [Effect Eff] (I : (e : Eff) → EStateM ε σ (Effect.ret e))
    (e : Eff) (cont : Effect.ret e → FreeM Eff α) (s s' : σ) (v : Effect.ret e) (h : I e s = .ok v s') :
    (FreeM.liftM I (FreeM.impure e cont)).run s = (FreeM.liftM I (cont v)).run s' := by
  show EStateM.bind (I e) (fun res => FreeM.liftM I (cont res)) s = _
  simp only [EStateM.bind, h]
  rfl

theorem runF_impure_gen {α : Type} (eff : InstructionEffect)
    (cont : InstructionEffect.ret eff → FreeM ((Except (Sail.Error exception) InstructionEffect) ⊕ FinChoice) α)
    (s s' : FState) (v : InstructionEffect.ret eff) (h : interpEff eff s = .ok v s') :
    runF (FreeM.impure (.inl (.ok eff)) cont) s = runF (cont v) s' := by
  rw [runF_def, runF_def]
  exact liftM_impure_gen _ (Sum.inl (Except.ok eff) : (Except (Sail.Error exception) InstructionEffect) ⊕ FinChoice) cont s s' v h

theorem oracleEff_sound (K : Known) (s : FState) (hK : K.Agrees s) (eff : InstructionEffect)
    (v : InstructionEffect.ret eff) (K1 : Known) (h : oracleEff K eff = some (v, K1)) :
    ∃ s1, interpEff eff s = .ok v s1 ∧ K1.Agrees s1 ∧
      (∀ r, K1.regs r = none → s1.regs r = s.regs r) ∧
      (∀ r, (K.regs r).isSome → (K1.regs r).isSome) := by
  cases eff with
  | regRead reg acc =>
    simp only [oracleEff] at h
    split at h
    · rename_i w hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨s, ?_, hK, fun _ _ => rfl, fun _ h => h⟩
      show EStateM.Result.ok (s.regs reg) s = EStateM.Result.ok _ s
      exact congrArg (fun x => EStateM.Result.ok x s) (hK.1 reg _ hr)
    · simp at h
  | regWrite reg acc v' =>
    simp only [oracleEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨s.set reg v', rfl, Known.agrees_set K s hK reg v', ?_, ?_⟩
    · intro r hr
      by_cases h : reg = r
      · subst h
        simp [Known.set] at hr
      · simp [FState.set, h]
    · intro r hr
      by_cases h : reg = r
      · subst h
        simp [Known.set]
      · simpa [Known.set, h] using hr
  | memRead req =>
    simp only [oracleEff] at h
    cases hb : readAnswer K req with
    | none => simp [hb] at h
    | some w =>
      simp [hb] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨s, ?_, hK, fun _ _ => rfl, fun _ h => h⟩
      have hw := readAnswer_sound K s hK req w hb
      subst hw
      rfl
  | memWrite req v' tags =>
    simp only [oracleEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨{ s with mem := writeBytes s.mem req.address.toNat req.size v' }, rfl,
      ⟨fun r w hw => hK.1 r w hw, fun i b hb => by simp at hb, by simp [hK.2.2]⟩,
      fun _ _ => rfl, fun _ h => h⟩
  | getCycleCount =>
    simp only [oracleEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, rfl, hK, fun _ _ => rfl, fun _ h => h⟩
  | barrier _ | cacheOp _ | tlbOp _ | translationStart _ | translationEnd _ | archException _
  | returnException | memWriteAnnounce _ | printMessage _ | clockCycle =>
    simp only [oracleEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, rfl, hK, fun _ _ => rfl, fun _ h => h⟩

theorem oracleGo_sound {α : Type} : ∀ (n : Nat) (K : Known) (s : FState) (m : SailM α) (a : α) (K' : Known),
    K.Agrees s → oracleGo n K m = some (a, K') →
    ∃ s', runF m s = .ok a s' ∧ K'.Agrees s' ∧ s'.mem = K'.data ∧
      (∀ r, K'.regs r = none → s'.regs r = s.regs r) ∧
      (∀ r, (K.regs r).isSome → (K'.regs r).isSome) := by
  intro n
  induction n with
  | zero => intro K s m a K' hK h; simp [oracleGo] at h
  | succ n ih =>
    intro K s m a K' hK h
    match m with
    | .pure x =>
      simp only [oracleGo, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s, runF_pure _ s, hK, hK.2.2.symm, fun _ _ => rfl, fun _ h => h⟩
    | .impure (.inl (.error e)) cont => simp [oracleGo] at h
    | .impure (.inl (.ok eff)) cont =>
      simp only [oracleGo] at h
      cases hv : oracleEff K eff with
      | none => simp [hv] at h
      | some p =>
        obtain ⟨v, K1⟩ := p
        simp only [hv, Option.bind_some] at h
        obtain ⟨s1, hs1, hK1, hf1, hmono1⟩ := oracleEff_sound K s hK eff v K1 hv
        obtain ⟨s', hs', hK', hm', hf', hmono'⟩ := ih K1 s1 (cont v) a K' hK1 h
        refine ⟨s', ?_, hK', hm', ?_, ?_⟩
        · rw [runF_impure_gen eff cont s s1 v hs1]
          exact hs'
        · intro r hr
          have hK1r : K1.regs r = none := by
            cases h1 : K1.regs r with
            | none => rfl
            | some w =>
              have := hmono' r (by simp [h1])
              simp [hr] at this
          rw [hf' r hr, hf1 r hK1r]
        · intro r hr
          exact hmono' r (hmono1 r hr)
    | .impure (.inr k) cont =>
      simp only [oracleGo] at h
      by_cases hk0 : @LT.lt Nat instLTNat 0 k
      · rw [dif_pos hk0] at h
        rw [runF_choice_pos k hk0 cont s]
        exact ih K s _ a K' hK h
      · rw [dif_neg hk0] at h
        simp at h

theorem runOracleW_sound {α : Type} (K : Known) (s : FState) (m : SailM α) (a : α) (K' : Known)
    (hK : K.Agrees s) (h : runOracleW K m = some (a, K')) :
    ∃ s', runF m s = .ok a s' ∧ K'.Agrees s' ∧ s'.mem = K'.data ∧
      (∀ r, K'.regs r = none → s'.regs r = s.regs r) ∧
      (∀ r, (K.regs r).isSome → (K'.regs r).isSome) :=
  oracleGo_sound oracleFuel K s m a K' hK h

/-! Write log: a register whose value changed during the run is in `wr`. -/

theorem oracleEff_wr (K : Known) (eff : InstructionEffect) (v : InstructionEffect.ret eff) (K1 : Known)
    (h : oracleEff K eff = some (v, K1)) :
    (∀ r ∈ K.wr, r ∈ K1.wr) ∧ (∀ r, K1.regs r ≠ K.regs r → r ∈ K1.wr) := by
  cases eff with
  | regRead reg acc =>
    simp only [oracleEff] at h
    split at h
    · rename_i w hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨fun r hr => hr, fun r hr => absurd rfl hr⟩
    · simp at h
  | regWrite reg acc v' =>
    simp only [oracleEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨fun r hr => List.mem_cons_of_mem _ hr, fun r hr => ?_⟩
    by_cases h : reg = r
    · subst h; exact List.mem_cons_self
    · exfalso; apply hr; simp [Known.set, h]
  | memRead req =>
    simp only [oracleEff] at h
    cases hb : readAnswer K req with
    | none => simp [hb] at h
    | some w =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨fun r hr => hr, fun r hr => absurd rfl hr⟩
  | memWrite req v' tags =>
    simp only [oracleEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun r hr => hr, fun r hr => absurd rfl hr⟩
  | getCycleCount =>
    simp only [oracleEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun r hr => hr, fun r hr => absurd rfl hr⟩
  | barrier _ | cacheOp _ | tlbOp _ | translationStart _ | translationEnd _ | archException _
  | returnException | memWriteAnnounce _ | printMessage _ | clockCycle =>
    simp only [oracleEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun r hr => hr, fun r hr => absurd rfl hr⟩

theorem oracleGo_wr {α : Type} : ∀ (n : Nat) (K : Known) (m : SailM α) (a : α) (K' : Known),
    oracleGo n K m = some (a, K') → (∀ r ∈ K.wr, r ∈ K'.wr) ∧ (∀ r, K'.regs r ≠ K.regs r → r ∈ K'.wr) := by
  intro n
  induction n with
  | zero => intro K m a K' h; simp [oracleGo] at h
  | succ n ih =>
    intro K m a K' h
    match m with
    | .pure x =>
      simp only [oracleGo, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨fun r hr => hr, fun r hr => absurd rfl hr⟩
    | .impure (.inl (.error e)) cont => simp [oracleGo] at h
    | .impure (.inl (.ok eff)) cont =>
      simp only [oracleGo] at h
      cases hv : oracleEff K eff with
      | none => simp [hv] at h
      | some p =>
        obtain ⟨v, K1⟩ := p
        simp only [hv, Option.bind_some] at h
        obtain ⟨hm1, hd1⟩ := oracleEff_wr K eff v K1 hv
        obtain ⟨hm2, hd2⟩ := ih K1 (cont v) a K' h
        refine ⟨fun r hr => hm2 r (hm1 r hr), fun r hr => ?_⟩
        by_cases hk : K1.regs r = K.regs r
        · exact hd2 r (fun h' => hr (h'.trans hk))
        · exact hm2 r (hd1 r hk)
    | .impure (.inr k) cont =>
      simp only [oracleGo] at h
      by_cases hk0 : @LT.lt Nat instLTNat 0 k
      · rw [dif_pos hk0] at h
        exact ih K _ a K' h
      · rw [dif_neg hk0] at h
        simp at h

/-- Registers outside `K'.wr` keep the value they had before the run. -/
theorem runOracleW_frame {α : Type} (K : Known) (m : SailM α) (a : α) (K' : Known)
    (h : runOracleW K m = some (a, K')) (r : Register) (hr : r ∉ K'.wr) : K'.regs r = K.regs r := by
  refine Classical.byContradiction fun hne => hr ((oracleGo_wr oracleFuel K m a K' h).2 r (fun e => hne e))

end Slop.Wr
