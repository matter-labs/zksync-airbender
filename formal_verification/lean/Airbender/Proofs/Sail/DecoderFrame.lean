import Airbender.Proofs.Sail.PC

namespace Airbender.Reference.Sail
open Reference.RiscV.Sail _root_.Sail.ArchSem

/-- A property of the existing Sail interpreter: successful execution preserves
    state and can be replayed in any state with the same `misa` image. -/
private def MisaOnly {α : Type} (action : SailRV32.SailM α) : Prop :=
  ∀ before value after, run action before = .ok value after →
    after = before ∧ ∀ state, state.regs.get? .misa = before.regs.get? .misa →
      run action state = .ok value state

private theorem misa_pure {α : Type} (value : α) : MisaOnly (pure value) := by
  intro before actual after executed
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj executed
  exact ⟨rfl, fun _ _ => rfl⟩

private theorem misa_bind {α β : Type} (action : SailRV32.SailM α)
    (next : α → SailRV32.SailM β) (first : MisaOnly action)
    (rest : ∀ value, MisaOnly (next value)) : MisaOnly (action >>= next) := by
  intro before value after executed
  cases initial : run action before with
  | error error middle =>
    rw [run_bind_of_error _ _ _ _ _ initial] at executed
    cases executed
  | ok input middle =>
    obtain ⟨unchanged, replay⟩ := first before input middle initial
    subst middle
    rw [run_bind_of_ok _ _ _ _ _ initial] at executed
    obtain ⟨unchanged, finish⟩ := rest input before value after executed
    subst after
    refine ⟨rfl, fun state same => ?_⟩
    rw [run_bind_of_ok _ _ _ _ _ (replay state same)]
    exact finish state same

private theorem misa_read : MisaOnly (SailRV32.readReg .misa) := by
  intro before value after executed
  cases found : before.regs.get? .misa with
  | none =>
    dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects,
      FreeM.liftM, interpretInstructionEffect] at executed
    simp only [found] at executed
    change EStateM.Result.error (_root_.Sail.Error.Unreachable) before =
      EStateM.Result.ok value after at executed
    cases executed
  | some data =>
    have read := read_register found
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (read.symm.trans executed)
    refine ⟨rfl, fun state equal => ?_⟩
    exact read_register equal

private theorem misa_ite {α : Type} (condition : Prop) [Decidable condition]
    (yes no : SailRV32.SailM α) (hy : MisaOnly yes) (hn : MisaOnly no) :
    MisaOnly (if condition then yes else no) := by
  by_cases selected : condition <;> simp [selected, hy, hn]

private theorem misa_assert (condition : Bool) (message : String) :
    MisaOnly (SailRV32.assert condition message) := by
  cases condition
  · intro before value after executed
    cases executed
  · exact misa_pure ()

private theorem misa_throw {α : Type} (error : _root_.Sail.Error SailRV32.exception) :
    MisaOnly (throw error : SailRV32.SailM α) := by
  intro before value after executed
  cases executed

attribute [irreducible] MisaOnly

set_option backward.isDefEq.respectTransparency false in
private theorem misa_enabled (extension : SailRV32.extension)
    (supported : extension ∈ [SailRV32.extension.Ext_M, .Ext_Zmmul, .Ext_Zba, .Ext_Zbb, .Ext_B,
      .Ext_Zbkb, .Ext_Zicsr, .Ext_Zimop, .Ext_Sv32, .Ext_Sv39, .Ext_Sv48, .Ext_Sv57]) :
    MisaOnly (SailRV32.Functions.currentlyEnabled extension) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [SailRV32.Functions.currentlyEnabled]
  all_goals
    repeat' first
      | exact misa_read
      | apply misa_pure
      | apply misa_assert
      | apply misa_throw
      | (apply misa_bind <;> try intro)

set_option backward.isDefEq.respectTransparency false in
private theorem misa_virtual : MisaOnly (SailRV32.Functions.virtual_memory_supported ()) := by
  unfold SailRV32.Functions.virtual_memory_supported
  repeat' first
    | (apply misa_enabled; simp)
    | apply misa_pure
    | (apply misa_bind <;> try intro)

set_option backward.isDefEq.respectTransparency false in
private theorem misa_register (bits : BitVec 5) :
    MisaOnly (SailRV32.Functions.encdec_reg_backwards bits) := by
  unfold SailRV32.Functions.encdec_reg_backwards
  apply misa_pure

set_option backward.isDefEq.respectTransparency false in
private theorem misa_opcodes :
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_bop_backwards bits)) ∧
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_iop_backwards bits)) ∧
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_mul_op_backwards bits)) ∧
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_uop_backwards bits)) ∧
    (∀ bits, MisaOnly (SailRV32.Functions.encdec_csrop_backwards bits)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro bits
  all_goals
    simp only [SailRV32.Functions.encdec_bop_backwards, SailRV32.Functions.encdec_iop_backwards,
      SailRV32.Functions.encdec_mul_op_backwards, SailRV32.Functions.encdec_uop_backwards,
      SailRV32.Functions.encdec_csrop_backwards]
    repeat' first
      | apply misa_pure
      | apply misa_assert
      | apply misa_throw
      | (apply misa_bind <;> try intro)
      | apply misa_ite
      | split

private theorem misa_share {α β γ : Type} (next : α → SailRV32.SailM β)
    (body : (α → SailRV32.SailM β) → SailRV32.SailM γ)
    (valid : ∀ value, MisaOnly (next value))
    (rest : ∀ next, (∀ value, MisaOnly (next value)) → MisaOnly (body next)) :
    MisaOnly (body next) := rest next valid

local elab "misa_source_step" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``MisaOnly 2 do
    throwError "expected a MisaOnly goal"
  let action := target.appArg!.consumeMData
  if let .letE name type value body _ := action then
    if value.isLambda then
      let abstraction := Lean.mkLambda name .default type body
      let shared ← goal.withContext <| Lean.Meta.mkAppM ``misa_share #[value, abstraction]
      let [validGoal, restGoal] ← goal.apply shared
        | throwError "expected the continuation and its body"
      let (_, validGoal) ← validGoal.intro1
      let (_, restGoal) ← restGoal.intro1
      let (_, restGoal) ← restGoal.intro1
      Lean.Elab.Tactic.replaceMainGoal [validGoal, restGoal]
    else
      Lean.Elab.Tactic.replaceMainGoal
        [← goal.replaceTargetDefEq (Lean.mkApp target.appFn! (body.instantiate1 value))]
    return
  if action.getAppFn.isFVar then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply_assumption))
    return
  match action.getAppFn.constName? with
  | some ``SailRV32.Functions.encdec_reg_backwards =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact misa_register _))
  | some ``SailRV32.Functions.encdec_bop_backwards =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact misa_opcodes.1 _))
  | some ``SailRV32.Functions.encdec_iop_backwards =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact misa_opcodes.2.1 _))
  | some ``SailRV32.Functions.encdec_mul_op_backwards =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact misa_opcodes.2.2.1 _))
  | some ``SailRV32.Functions.encdec_uop_backwards =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact misa_opcodes.2.2.2.1 _))
  | some ``SailRV32.Functions.encdec_csrop_backwards =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact misa_opcodes.2.2.2.2 _))
  | some ``SailRV32.Functions.virtual_memory_supported =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact misa_virtual))
  | some ``SailRV32.Functions.currentlyEnabled =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply misa_enabled; simp))
  | _ =>
    let reduced := action.headBeta
    if action == reduced then
      throwError "no source step or head beta reduction"
    Lean.Elab.Tactic.replaceMainGoal
      [← goal.replaceTargetDefEq (Lean.mkApp target.appFn! reduced)]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
/-- Successful original Sail decoding changes no state. Its result is unchanged
    in any state with the same `misa` image, including native GPR/PC updates. -/
theorem decoded_misa_frame (bits : BitVec 32) {before after : State}
    {instruction : SailRV32.instruction}
    (decoded : run (SailRV32.Functions.encdec_backwards bits) before = .ok instruction after) :
    after = before ∧ ∀ state, state.regs.get? .misa = before.regs.get? .misa →
      run (SailRV32.Functions.encdec_backwards bits) state = .ok instruction state := by
  have checked : MisaOnly (SailRV32.Functions.encdec_backwards bits) := by
    unfold SailRV32.Functions.encdec_backwards
    repeat' first
      | misa_source_step
      | assumption
      | apply misa_pure
      | apply misa_assert
      | apply misa_throw
      | (apply misa_bind <;> try intro)
      | apply misa_ite
      | split
  unfold MisaOnly at checked
  exact checked before instruction after decoded

end Airbender.Reference.Sail
