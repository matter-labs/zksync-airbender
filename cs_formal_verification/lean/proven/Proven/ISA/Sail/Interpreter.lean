import Proven.ISA.Sail.InterpreterBytes

/-! `runSail` simulates lean-sail's `interpretSailEffects`: one case per effect, then induction on the program. -/

open Sail Sail.ArchSem SailRV32 Human

namespace Proven.Interpreter
open Airbender

/-- A register write keeps the agreement. -/
theorem set_agrees {state : SailState} {sequential : SequentialSailState}
    (agrees : SequentialAgrees state sequential) (register : Register) (value : RegisterType register) :
    SequentialAgrees (state.set register value) { sequential with regs := sequential.regs.insert register value } := by
  refine ⟨?_, agrees.mem⟩
  intro other result present
  change (state.set register value).regs other = result
  by_cases same : register = other
  · subst same
    rw [Std.ExtDHashMap.get?_insert_self] at present
    cases present
    simp [SailState.set]
  · rw [Std.ExtDHashMap.get?_insert, dite_eq_right_of_eq_false (by simpa using same)] at present
    simp only [SailState.set, dite_eq_right_of_eq_false (eq_false same)]
    exact agrees.regs other result present

/-- `runSail` runs one effect, then the continuation. -/
theorem runSail_effect {α : Type} (effect : InstructionEffect) (next : effect.ret → SailM α) (state : SailState) :
    runSail (.impure (.inl (.ok effect)) next) state =
      match applyEffect effect state with
      | .ok value state' => runSail (next value) state'
      | .error error state' => .error error state' := by
  unfold runSail
  simp only [FreeM.liftM, bind, EStateM.bind, EStateM.run]
  generalize applyEffect effect state = result
  cases result <;> rfl

/-- lean-sail runs one effect, then the continuation. -/
theorem sequential_effect {α : Type} (effect : InstructionEffect) (next : effect.ret → SailM α)
    (sequential : SequentialSailState) :
    (interpretSailEffects (.impure (.inl (.ok effect)) next : SailM α)).run sequential =
      match interpretInstructionEffect (ue := exception) effect sequential with
      | .ok value sequential' => (interpretSailEffects (next value)).run sequential'
      | .error error sequential' => .error error sequential' := by
  unfold interpretSailEffects
  simp only [FreeM.liftM, bind, EStateM.bind, EStateM.run]
  generalize interpretInstructionEffect (ue := exception) effect sequential = result
  cases result <;> rfl

/-- `runSail` resolves a finite choice to its first option. -/
theorem runSail_choice {α : Type} (choices : Nat) (next : Fin choices → SailM α) (state : SailState) :
    runSail (.impure (.inr choices) next) state =
      if positive : 0 < choices then runSail (next ⟨0, positive⟩) state else .error .Unreachable state := by
  unfold runSail
  by_cases positive : 0 < choices
  · simp only [FreeM.liftM, bind, EStateM.bind, EStateM.run, positive, ↓reduceDIte]
    rfl
  · simp only [FreeM.liftM, bind, EStateM.bind, EStateM.run, positive, ↓reduceDIte]
    rfl

/-- lean-sail resolves a finite choice to its first option. -/
theorem sequential_choice {α : Type} (choices : Nat) (next : Fin choices → SailM α)
    (sequential : SequentialSailState) :
    (interpretSailEffects (.impure (.inr choices) next : SailM α)).run sequential =
      if positive : 0 < choices then (interpretSailEffects (next ⟨0, positive⟩)).run sequential
      else .error .Unreachable sequential := by
  unfold interpretSailEffects
  by_cases positive : 0 < choices
  · simp only [FreeM.liftM, bind, EStateM.bind, EStateM.run, positive, ↓reduceDIte]
    rfl
  · simp only [FreeM.liftM, bind, EStateM.bind, EStateM.run, positive, ↓reduceDIte]
    rfl

/-- The `runSail` result and the lean-sail result agree, or lean-sail stops on missing data. -/
def Matches {α : Type} : EStateM.Result (Sail.Error exception) SailState α →
    EStateM.Result (Sail.Error exception) SequentialSailState α → Prop
  | .ok value state, .ok value' sequential => value = value' ∧ SequentialAgrees state sequential
  | .error error _, .error error' _ => error = error' ∨ MissingData error'
  | .ok _ _, .error error _ => MissingData error
  | .error _ _, .ok _ _ => False

/-- One effect: `applyEffect` succeeds. lean-sail gives the same result, or it stops on missing data. -/
theorem effect_simulation (effect : InstructionEffect) (other : effect ≠ .getCycleCount)
    {state : SailState} {sequential : SequentialSailState} (agrees : SequentialAgrees state sequential) :
    ∃ result state', applyEffect effect state = .ok result state' ∧
      ((∃ sequential', interpretInstructionEffect (ue := exception) effect sequential = .ok result sequential' ∧
          SequentialAgrees state' sequential') ∨
        ∃ error sequential', interpretInstructionEffect (ue := exception) effect sequential = .error error sequential' ∧
          MissingData error) := by
  cases effect with
  | regRead register access =>
    refine ⟨state.regs register, state, rfl, ?_⟩
    cases present : sequential.regs.get? register with
    | none =>
      right
      refine ⟨.Unreachable, sequential, ?_, trivial⟩
      simp only [interpretInstructionEffect, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
        present]
      rfl
    | some value =>
      left
      refine ⟨sequential, ?_, agrees⟩
      simp only [interpretInstructionEffect, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
        present, pure, EStateM.pure, agrees.regs register value present]
  | regWrite register access value =>
    exact ⟨(), state.set register value, rfl, Or.inl ⟨_, rfl, set_agrees agrees register value⟩⟩
  | memRead request =>
    refine ⟨.ok (readBytes state.mem request.address.toNat request.size, 0#request.numTag), state, rfl, ?_⟩
    by_cases tagged : request.numTag = 0
    · rcases sequential_readBytes agrees request.size request.address.toNat with read | ⟨missing, read⟩
      · left
        refine ⟨sequential, ?_, agrees⟩
        simp only [interpretInstructionEffect, bind, EStateM.bind, tagged, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure, read, BitVec.zero_eq]
      · right
        refine ⟨.OutOfMemoryRange missing, sequential, ?_, trivial⟩
        simp only [interpretInstructionEffect, bind, EStateM.bind, tagged, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte, read]
    · right
      refine ⟨.Assertion "Tagged memory not supported", sequential, ?_, rfl⟩
      have flag : (request.numTag != 0) = true := by simpa using tagged
      simp only [interpretInstructionEffect, bind, EStateM.bind, flag, ↓reduceIte, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw]
  | memWrite request value tags =>
    refine ⟨.ok (), { state with mem := writeBytes state.mem request.address.toNat request.size value }, rfl, ?_⟩
    by_cases tagged : request.numTag = 0
    · left
      refine ⟨_, ?_, write_agrees agrees request.address.toNat value⟩
      simp only [interpretInstructionEffect, bind, EStateM.bind, tagged, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, sequential_writeBytes, pure, EStateM.pure]
    · right
      refine ⟨.Assertion "Tagged memory not supported", sequential, ?_, rfl⟩
      have flag : (request.numTag != 0) = true := by simpa using tagged
      simp only [interpretInstructionEffect, bind, EStateM.bind, flag, ↓reduceIte, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw]
  | memWriteAnnounce request => exact ⟨(), state, rfl, Or.inl ⟨sequential, rfl, agrees⟩⟩
  | barrier kind => exact ⟨(), state, rfl, Or.inl ⟨sequential, rfl, agrees⟩⟩
  | cacheOp operation => exact ⟨(), state, rfl, Or.inl ⟨sequential, rfl, agrees⟩⟩
  | tlbOp operation => exact ⟨(), state, rfl, Or.inl ⟨sequential, rfl, agrees⟩⟩
  | clockCycle => exact ⟨(), state, rfl, Or.inl ⟨_, rfl, agrees.regs, agrees.mem⟩⟩
  | getCycleCount => exact absurd rfl other
  | translationStart start => exact ⟨(), state, rfl, Or.inl ⟨sequential, rfl, agrees⟩⟩
  | translationEnd finish => exact ⟨(), state, rfl, Or.inl ⟨sequential, rfl, agrees⟩⟩
  | archException exception => exact ⟨(), state, rfl, Or.inl ⟨sequential, rfl, agrees⟩⟩
  | returnException => exact ⟨(), state, rfl, Or.inl ⟨sequential, rfl, agrees⟩⟩
  | printMessage message => exact ⟨(), state, rfl, Or.inl ⟨_, rfl, agrees.regs, agrees.mem⟩⟩

/-- A lean-sail stop on missing data matches every `runSail` result. -/
theorem matches_missing {α : Type} (ours : EStateM.Result (Sail.Error exception) SailState α)
    {error : Sail.Error exception} (missing : MissingData error) (sequential : SequentialSailState) :
    Matches ours (.error error sequential) := by
  cases ours with
  | ok value state => exact missing
  | error error' state => exact Or.inr missing

/-- Every program without a cycle-counter read runs the same in `runSail` and in lean-sail,
    unless lean-sail stops on missing data. -/
theorem simulation {α : Type} {program : SailM α} (avoids : NoCycleRead program) :
    ∀ (state : SailState) (sequential : SequentialSailState), SequentialAgrees state sequential →
      Matches (runSail program state) ((interpretSailEffects program).run sequential) := by
  induction avoids with
  | pure value =>
    intro state sequential agrees
    exact ⟨rfl, agrees⟩
  | impure effect next other rest ih =>
    intro state sequential agrees
    rcases effect with (error | effect) | choices
    · exact Or.inl rfl
    · obtain ⟨result, state', ours, theirs⟩ :=
        effect_simulation effect (fun same => other (by rw [same])) agrees
      rw [runSail_effect, sequential_effect, ours]
      rcases theirs with ⟨sequential', theirs, agrees'⟩ | ⟨error, sequential', theirs, missing⟩
      · rw [theirs]
        exact ih result state' sequential' agrees'
      · rw [theirs]
        exact matches_missing _ missing sequential'
    · rw [runSail_choice choices next state, sequential_choice choices next sequential]
      by_cases positive : @LT.lt Nat instLTNat 0 choices
      · rw [dite_eq_left_of_eq_true (eq_true positive), dite_eq_left_of_eq_true (eq_true positive)]
        exact ih ⟨0, positive⟩ state sequential agrees
      · rw [dite_eq_right_of_eq_false (eq_false positive), dite_eq_right_of_eq_false (eq_false positive)]
        exact Or.inl rfl

/-- The two directions of the simulation. -/
theorem run_sail_simulation : RunSailSimulationClaim := by
  intro α program state sequential avoids agrees
  have matched := simulation avoids state sequential agrees
  constructor
  · intro value sequential' theirs
    rw [theirs] at matched
    cases ours : runSail program state with
    | ok value' state' =>
      rw [ours] at matched
      obtain ⟨same, agrees'⟩ := matched
      subst same
      exact ⟨state', rfl, agrees'⟩
    | error error state' =>
      rw [ours] at matched
      exact matched.elim
  · intro value state' ours
    rw [ours] at matched
    cases theirs : (interpretSailEffects program).run sequential with
    | ok value' sequential' =>
      rw [theirs] at matched
      obtain ⟨same, agrees'⟩ := matched
      subst same
      exact Or.inl ⟨sequential', rfl, agrees'⟩
    | error error sequential' =>
      rw [theirs] at matched
      exact Or.inr ⟨error, sequential', rfl, matched⟩

/-- The empty lean-sail state agrees with every `SailState`. -/
def emptySequential : SequentialSailState :=
  { regs := ∅, mem := ∅, tags := (), cycleCount := 0, sailOutput := #[] }

/-- Write the PC, then read it. -/
def writeReadPC : SailM (RegisterType .PC) :=
  .impure (.inl (.ok (.regWrite .PC none (4 : BitVec 32)))) fun _ =>
    .impure (.inl (.ok (.regRead .PC none))) .pure

/-- A register write and read run to completion in lean-sail from the empty state. -/
theorem run_sail_simulation_satisfiable : RunSailSimulationSatisfiableClaim := by
  refine ⟨writeReadPC, Airbender.Reference.RiscV.Sail.Configuration.resetState, emptySequential, (4 : BitVec 32),
    { emptySequential with regs := (∅ : Std.ExtDHashMap Register RegisterType).insert .PC (4 : BitVec 32) },
    ?_, ?_, ?_⟩
  · exact .impure _ _ (by intro same; cases same) fun _ =>
      .impure _ _ (by intro same; cases same) fun value => .pure value
  · refine ⟨fun register value present => ?_, fun address byte present => ?_⟩
    · simp [emptySequential] at present
    · simp [emptySequential] at present
  · change (match (EStateM.Result.ok () { emptySequential with
        regs := (∅ : Std.ExtDHashMap Register RegisterType).insert .PC (4 : BitVec 32) } :
          EStateM.Result (Sail.Error exception) SequentialSailState Unit) with
      | .ok _ sequential' => (interpretSailEffects (.impure (.inl (.ok (.regRead .PC none))) .pure :
          SailM (RegisterType .PC))).run sequential'
      | .error error sequential' => .error error sequential') = _
    simp only [interpretSailEffects, FreeM.liftM, interpretInstructionEffect, bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, Std.ExtDHashMap.get?_insert_self, pure, EStateM.pure, EStateM.run]

end Proven.Interpreter
