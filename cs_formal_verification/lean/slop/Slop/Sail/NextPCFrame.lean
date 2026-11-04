import Slop.Sail.ExecRun

/-! # Frame: register-only Sail computations that never write `nextPC` leave `nextPC` alone

`RegFrame m`: every effect of `m` is a register read, or a register write to a register other than `nextPC`.
The generated AddSub clauses are such computations; `runSail` then keeps `nextPC` (the `hal` obligation of
`step_of_exec` after `execution_hexec`). -/

namespace Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem Configuration Airbender.Reference.Sail SailRV32 SailRV32.Functions

/-- Effects a frame computation may perform. -/
def FrameEff {ue : Type} : (Except (Sail.Error ue) InstructionEffect ⊕ FinChoice) → Prop
  | .inl (.ok (.regRead _ _)) => True
  | .inl (.ok (.regWrite reg _ _)) => reg ≠ .nextPC
  | _ => False

/-- A computation whose every effect is a frame effect. -/
inductive RegFrame {ue α : Type} : PreSailM ue α → Prop
  | pure (a : α) : RegFrame (FreeM.pure a)
  | impure (e) (k : Effect.ret e → PreSailM ue α) : FrameEff e → (∀ x, RegFrame (k x)) → RegFrame (FreeM.impure e k)

theorem set_regs_ne (σ : SailState) (r : Register) (v : RegisterType r) (h : r ≠ .nextPC) :
    (σ.set r v).regs .nextPC = σ.regs .nextPC := by
  unfold SailState.set
  dsimp only
  rw [dite_eq_right]
  exact fun hh => absurd hh h

/-- A successful bind splits into its two successful halves (generic `EStateM`). -/
theorem estate_bind_split {ε σ α β : Type} (x : EStateM ε σ α) (f : α → EStateM ε σ β) {s : σ} {v : β} {s' : σ}
    (h : (x >>= f).run s = .ok v s') : ∃ a s1, x.run s = .ok a s1 ∧ (f a).run s1 = .ok v s' := by
  unfold EStateM.run at h ⊢
  change EStateM.bind x f s = _ at h
  unfold EStateM.bind at h
  split at h
  · rename_i a s1 hx
    exact ⟨a, s1, hx, h⟩
  · cases h

/-- Frame computations keep `nextPC`. -/
theorem regFrame_nextPC {α : Type} (m : SailRV32.SailM α) (hm : RegFrame m) (σ σ' : SailState) (v : α)
    (h : runSail m σ = .ok v σ') : σ'.regs .nextPC = σ.regs .nextPC := by
  induction hm generalizing σ σ' v with
  | pure a =>
    change EStateM.Result.ok a σ = _ at h
    cases h
    rfl
  | impure e k hfe hk ih =>
    unfold runSail at h
    cases e with
    | inl r =>
      cases r with
      | error err => simp [FrameEff] at hfe
      | ok eff =>
        cases eff with
        | regRead reg acc =>
          change (Configuration.applyEffect (InstructionEffect.regRead reg acc) >>= fun res => FreeM.liftM _ (k res)).run σ = _ at h
          obtain ⟨res, σ1, hx, hk'⟩ := estate_bind_split _ _ h
          have hσ1 : σ1 = σ := by
            simp only [Configuration.applyEffect, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure,
              EStateM.pure, EStateM.run] at hx
            cases hx; rfl
          rw [hσ1] at hk'
          exact ih res σ σ' v (by unfold runSail; exact hk')
        | regWrite reg acc val =>
          have hne : reg ≠ .nextPC := hfe
          change (Configuration.applyEffect (InstructionEffect.regWrite reg acc val) >>= fun res => FreeM.liftM _ (k res)).run σ = _ at h
          obtain ⟨res, σ1, hx, hk'⟩ := estate_bind_split _ _ h
          have hσ1 : σ1 = σ.set reg val := by
            simp only [Configuration.applyEffect, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.run]
              at hx
            cases hx; rfl
          rw [hσ1] at hk'
          have := ih res (σ.set reg val) σ' v (by unfold runSail; exact hk')
          rw [this, set_regs_ne σ reg val hne]
        | _ => simp [FrameEff] at hfe
    | inr n => simp [FrameEff] at hfe

theorem frame_pure {ue α : Type} (a : α) : RegFrame (FreeM.pure a : PreSailM ue α) := RegFrame.pure a

theorem frame_bind {ue α β : Type} {m : PreSailM ue α} {k : α → PreSailM ue β} (hm : RegFrame m)
    (hk : ∀ x, RegFrame (k x)) : RegFrame (FreeM.bind m k) := by
  induction hm with
  | pure a => exact hk a
  | impure e k' hc hkk ih => exact RegFrame.impure e _ hc (fun x => ih x)

theorem frame_readReg {ue : Type} (r : Register) : RegFrame (PreSail.readReg (ue := ue) r) :=
  RegFrame.impure _ _ trivial (fun x => RegFrame.pure x)

theorem frame_writeReg {ue : Type} (r : Register) (v : Arch.register_type r) (h : r ≠ .nextPC) :
    RegFrame (PreSail.writeReg (ue := ue) r v) :=
  RegFrame.impure (.inl (.ok (InstructionEffect.regWrite r Option.none v))) _ h (fun x => RegFrame.pure x)

macro "frame_base" : tactic => `(tactic| repeat' (first
  | exact frame_pure _
  | exact frame_readReg _
  | exact frame_writeReg _ _ (by intro h; cases h)
  | apply frame_bind
  | intro _
  | split))

theorem frame_rX (r : regno) : RegFrame (rX r) := by
  unfold rX; frame_base

theorem frame_wX (r : regno) (v : BitVec 32) : RegFrame (wX r v) := by
  unfold wX; frame_base

theorem frame_rX_bits (r : regidx) : RegFrame (rX_bits r) := by
  unfold rX_bits; dsimp only; exact frame_rX _

theorem frame_wX_bits (r : regidx) (v : BitVec 32) : RegFrame (wX_bits r v) := by
  unfold wX_bits; dsimp only; exact frame_wX _ _

theorem frame_get_arch_pc : RegFrame (get_arch_pc ()) := by
  unfold get_arch_pc; exact frame_readReg _

macro "frame_exec" : tactic => `(tactic| repeat' (first
  | exact frame_pure _
  | exact frame_readReg _
  | exact frame_writeReg _ _ (by intro h; cases h)
  | exact frame_rX_bits _
  | exact frame_wX_bits _ _
  | exact frame_get_arch_pc
  | apply frame_bind
  | intro _
  | split))

theorem frame_execute_RTYPE (rs2 rs1 rd : regidx) (op : rop) : RegFrame (execute_RTYPE rs2 rs1 rd op) := by
  unfold execute_RTYPE; dsimp only; cases op <;> frame_exec

theorem frame_execute_ITYPE (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    RegFrame (execute_ITYPE imm rs1 rd op) := by
  unfold execute_ITYPE; dsimp only; cases op <;> frame_exec

theorem frame_execute_UTYPE (imm : BitVec 20) (rd : regidx) (op : uop) :
    RegFrame (execute_UTYPE imm rd op) := by
  unfold execute_UTYPE; dsimp only; cases op <;> frame_exec

/-- The five AddSub-family clauses selected by `Reference.execution` are register-only, and never write `nextPC`. -/
theorem frame_execution (input : Input) : RegFrame (execution input) := by
  unfold execution
  cases h : input.row.opcode <;> simp only [instruction, registerClause, h, Option.get_some]
  · exact frame_execute_RTYPE _ _ _ _
  · exact frame_execute_ITYPE _ _ _ _
  · exact frame_execute_RTYPE _ _ _ _
  · exact frame_execute_UTYPE _ _ _
  · exact frame_execute_UTYPE _ _ _

/-- After the AddSub clause, `nextPC` still holds the `PC + 4` that `normalBaseNextPC` assigned. -/
theorem execution_nextPC (input : Input) (σ σ2 : SailState)
    (h : runSail (execution input) (σ.set .nextPC (σ.regs .PC + 4)) = .ok SailRV32.Functions.RETIRE_SUCCESS σ2) :
    σ2.regs .nextPC = σ.regs .PC + 4 := by
  rw [regFrame_nextPC _ (frame_execution input) _ _ _ h]
  simp [SailState.set]

end Airbender.Reference.RiscV.Sail
