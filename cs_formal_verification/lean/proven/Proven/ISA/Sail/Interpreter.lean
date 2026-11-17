import Proven.ISA.Sail.InterpreterBytes
import Proven.ISA.Sail.Oracle

/-! `runSail` and lean-sail's `interpretSailEffects`: one case per effect, then induction on the program. The same
    induction shows that `runSail` reads only the registers, the cycle counter and the bytes that a request can
    reach. -/

open Sail Sail.ArchSem SailRV32 Human

namespace Proven.Interpreter
open Airbender Airbender.Reference.RiscV.Sail.Configuration

/-! ## One step of each interpreter -/

/-- `runSail` stops on an error effect. -/
theorem runSail_error {α : Type} (error : Sail.Error exception) (next : Empty → SailM α) (state : SailState) :
    runSail (.impure (.inl (.error error)) next) state = .error error state := by
  unfold runSail
  simp only [FreeM.liftM, bind, EStateM.bind, EStateM.run]
  rfl

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

/-! ## Memory requests -/

/-- A request with tags fails the request checks. -/
theorem checkRequest_tagged {req : MemRequest} (tagged : req.numTag ≠ 0) (state : SailState) :
    checkRequest req state = .error (.Assertion "Tagged memory not supported") state := by
  have flag : (req.numTag != 0) = true := by simpa using tagged
  simp only [checkRequest, flag, ↓reduceIte, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-- A request with more than `maxRequestBytes` bytes fails the request checks. -/
theorem checkRequest_large {req : MemRequest} (untagged : req.numTag = 0) (large : maxRequestBytes < req.size)
    (state : SailState) : checkRequest req state = .error (.OutOfMemoryRange req.address.toNat) state := by
  have flag : (req.numTag != 0) = false := by simp [untagged]
  simp only [checkRequest, flag, large, Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-- A memory read stops when its request fails the checks. -/
theorem applyEffect_memRead_error (req : MemRequest) (state state' : SailState) (error : Sail.Error exception)
    (failed : checkRequest req state = .error error state') :
    applyEffect (.memRead req) state = .error error state' := by
  simp only [Airbender.Reference.RiscV.Sail.Configuration.applyEffect, bind, EStateM.bind, failed]

/-- A memory write stops when its request fails the checks. -/
theorem applyEffect_memWrite_error (req : MemRequest) (value : BitVec (8 * req.size)) (tags : BitVec req.numTag)
    (state state' : SailState) (error : Sail.Error exception) (failed : checkRequest req state = .error error state') :
    applyEffect (.memWrite req value tags) state = .error error state' := by
  simp only [Airbender.Reference.RiscV.Sail.Configuration.applyEffect, bind, EStateM.bind, failed]

/-- A request that passes the checks reaches only bytes below `requestReach`. -/
theorem request_reach (req : MemRequest) (small : req.size ≤ maxRequestBytes) (index : Nat)
    (bound : index < req.size) : req.address.toNat + index < requestReach := by
  have address : req.address.toNat < 2 ^ 34 := req.address.isLt
  unfold requestReach
  omega

/-! ## `runSail` to lean-sail -/

/-- A register write keeps the agreement. -/
theorem set_agrees {state : SailState} {sequential : SequentialSailState}
    (agrees : SequentialAgrees state sequential) (register : Register) (value : RegisterType register) :
    SequentialAgrees (state.set register value) { sequential with regs := sequential.regs.insert register value } := by
  refine ⟨?_, agrees.mem, agrees.cycles⟩
  intro other
  by_cases same : register = other
  · subst same
    rw [Std.ExtDHashMap.get?_insert_self]
    simp [SailState.set]
  · rw [Std.ExtDHashMap.get?_insert, dite_eq_right_of_eq_false (by simpa using same)]
    simp only [SailState.set, dite_eq_right_of_eq_false (eq_false same)]
    exact agrees.regs other

/-- One successful `runSail` effect is the same lean-sail effect, and the agreement holds after it. -/
theorem effect_transport (effect : InstructionEffect) {state state' : SailState} {sequential : SequentialSailState}
    (agrees : SequentialAgrees state sequential) {result : InstructionEffect.ret effect}
    (ours : applyEffect effect state = .ok result state') :
    ∃ sequential', interpretInstructionEffect (ue := exception) effect sequential = .ok result sequential' ∧
      SequentialAgrees state' sequential' := by
  cases effect with
  | regRead register access =>
    change EStateM.Result.ok (state.regs register) state = _ at ours
    cases ours
    refine ⟨sequential, ?_, agrees⟩
    simp only [interpretInstructionEffect, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      agrees.regs register, pure, EStateM.pure]
  | regWrite register access value =>
    change EStateM.Result.ok () (state.set register value) = _ at ours
    cases ours
    exact ⟨_, rfl, set_agrees agrees register value⟩
  | memRead req =>
    by_cases untagged : req.numTag = 0
    · by_cases small : req.size ≤ maxRequestBytes
      · rw [applyEffect_memRead req state (checkRequest_ok untagged small state)] at ours
        cases ours
        have read := sequential_readBytes state.mem req.size req.address.toNat fun index bound =>
          agrees.mem _ (request_reach req small index bound)
        refine ⟨sequential, ?_, agrees⟩
        simp only [interpretInstructionEffect, bind, EStateM.bind, untagged, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure, read, BitVec.zero_eq]
      · rw [applyEffect_memRead_error req state state _
          (checkRequest_large untagged (by omega) state)] at ours
        cases ours
    · rw [applyEffect_memRead_error req state state _ (checkRequest_tagged untagged state)] at ours
      cases ours
  | memWrite req value tags =>
    by_cases untagged : req.numTag = 0
    · by_cases small : req.size ≤ maxRequestBytes
      · rw [applyEffect_memWrite req value tags state (checkRequest_ok untagged small state)] at ours
        cases ours
        refine ⟨_, ?_, write_agrees agrees req.address.toNat value⟩
        simp only [interpretInstructionEffect, bind, EStateM.bind, untagged, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte, sequential_writeBytes, pure, EStateM.pure]
      · rw [applyEffect_memWrite_error req value tags state state _
          (checkRequest_large untagged (by omega) state)] at ours
        cases ours
    · rw [applyEffect_memWrite_error req value tags state state _ (checkRequest_tagged untagged state)] at ours
      cases ours
  | memWriteAnnounce request => cases ours; exact ⟨sequential, rfl, agrees⟩
  | barrier kind => cases ours; exact ⟨sequential, rfl, agrees⟩
  | cacheOp operation => cases ours; exact ⟨sequential, rfl, agrees⟩
  | tlbOp operation => cases ours; exact ⟨sequential, rfl, agrees⟩
  | clockCycle =>
    cases ours
    exact ⟨_, rfl, agrees.regs, agrees.mem, by simp [agrees.cycles]⟩
  | getCycleCount =>
    change EStateM.Result.ok state.cycles state = _ at ours
    cases ours
    refine ⟨sequential, ?_, agrees⟩
    simp only [interpretInstructionEffect, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, agrees.cycles]
  | translationStart start => cases ours; exact ⟨sequential, rfl, agrees⟩
  | translationEnd finish => cases ours; exact ⟨sequential, rfl, agrees⟩
  | archException exception => cases ours; exact ⟨sequential, rfl, agrees⟩
  | returnException => cases ours; exact ⟨sequential, rfl, agrees⟩
  | printMessage message => cases ours; exact ⟨_, rfl, agrees.regs, agrees.mem, agrees.cycles⟩

/-- Every successful `runSail` run is a successful lean-sail run with the same value. -/
theorem transport {α : Type} (program : SailM α) :
    ∀ (state state' : SailState) (sequential : SequentialSailState) (value : α),
      SequentialAgrees state sequential → runSail program state = .ok value state' →
      ∃ sequential', (interpretSailEffects program).run sequential = .ok value sequential' ∧
        SequentialAgrees state' sequential' := by
  induction program with
  | pure result =>
    intro state state' sequential value agrees ours
    change EStateM.Result.ok result state = _ at ours
    cases ours
    exact ⟨sequential, rfl, agrees⟩
  | impure effect next ih =>
    intro state state' sequential value agrees ours
    rcases effect with (error | effect) | choices
    · rw [runSail_error] at ours
      cases ours
    · rw [runSail_effect] at ours
      cases step : applyEffect effect state with
      | ok result middle =>
        rw [step] at ours
        obtain ⟨sequentialMiddle, theirs, agreesMiddle⟩ := effect_transport effect agrees step
        obtain ⟨sequential', run, agrees'⟩ := ih result middle state' sequentialMiddle value agreesMiddle ours
        refine ⟨sequential', ?_, agrees'⟩
        rw [sequential_effect, theirs]
        exact run
      | error error middle =>
        rw [step] at ours
        cases ours
    · rw [runSail_choice choices next state] at ours
      rw [sequential_choice choices next sequential]
      by_cases positive : @LT.lt Nat instLTNat 0 choices
      · rw [dite_eq_left_of_eq_true (eq_true positive)] at ours ⊢
        exact ih ⟨0, positive⟩ state state' sequential value agrees ours
      · rw [dite_eq_right_of_eq_false (eq_false positive)] at ours
        cases ours

/-! ## `runSail` reads only what lean-sail holds -/

/-- Two states with the same registers and cycle counter, and the same bytes that a request can reach. -/
structure Close (state other : SailState) : Prop where
  /-- The registers are equal. -/
  regs : state.regs = other.regs
  /-- The bytes that a request can reach are equal. -/
  mem : ∀ address, address < requestReach → state.mem address = other.mem address
  /-- The cycle counters are equal. -/
  cycles : state.cycles = other.cycles

/-- Two `runSail` results with the same value or error and close states. -/
def ResultClose {α : Type} : EStateM.Result (Sail.Error exception) SailState α →
    EStateM.Result (Sail.Error exception) SailState α → Prop
  | .ok value state, .ok value' other => value = value' ∧ Close state other
  | .error error state, .error error' other => error = error' ∧ Close state other
  | _, _ => False

/-- A register write keeps two states close. -/
theorem set_close {state other : SailState} (close : Close state other) (register : Register)
    (value : RegisterType register) : Close (state.set register value) (other.set register value) := by
  refine ⟨?_, close.mem, close.cycles⟩
  funext other'
  simp only [SailState.set, close.regs]

/-- A byte write keeps two states close. -/
theorem write_close {state other : SailState} (close : Close state other) (addr size : Nat)
    (value : BitVec (8 * size)) :
    Close { state with mem := writeBytes state.mem addr size value }
      { other with mem := writeBytes other.mem addr size value } := by
  refine ⟨close.regs, ?_, close.cycles⟩
  intro address reach
  change writeBytes state.mem addr size value address = writeBytes other.mem addr size value address
  rw [writeBytes_apply, writeBytes_apply]
  by_cases inside : addr ≤ address ∧ address < addr + size
  · rw [ite_eq_left inside, ite_eq_left inside]
  · rw [ite_eq_right inside, ite_eq_right inside]
    exact close.mem address reach

/-- One effect gives the same result on close states. -/
theorem effect_close (effect : InstructionEffect) {state other : SailState} (close : Close state other) :
    ResultClose (applyEffect effect state) (applyEffect effect other) := by
  cases effect with
  | regRead register access => exact ⟨congrFun close.regs register, close⟩
  | regWrite register access value => exact ⟨rfl, set_close close register value⟩
  | memRead req =>
    by_cases untagged : req.numTag = 0
    · by_cases small : req.size ≤ maxRequestBytes
      · rw [applyEffect_memRead req state (checkRequest_ok untagged small state),
          applyEffect_memRead req other (checkRequest_ok untagged small other)]
        refine ⟨?_, close⟩
        rw [readBytes_congr state.mem other.mem req.size req.address.toNat fun index bound =>
          close.mem _ (request_reach req small index bound)]
      · rw [applyEffect_memRead_error req state state _ (checkRequest_large untagged (by omega) state),
          applyEffect_memRead_error req other other _ (checkRequest_large untagged (by omega) other)]
        exact ⟨rfl, close⟩
    · rw [applyEffect_memRead_error req state state _ (checkRequest_tagged untagged state),
        applyEffect_memRead_error req other other _ (checkRequest_tagged untagged other)]
      exact ⟨rfl, close⟩
  | memWrite req value tags =>
    by_cases untagged : req.numTag = 0
    · by_cases small : req.size ≤ maxRequestBytes
      · rw [applyEffect_memWrite req value tags state (checkRequest_ok untagged small state),
          applyEffect_memWrite req value tags other (checkRequest_ok untagged small other)]
        exact ⟨rfl, write_close close req.address.toNat req.size value⟩
      · rw [applyEffect_memWrite_error req value tags state state _
            (checkRequest_large untagged (by omega) state),
          applyEffect_memWrite_error req value tags other other _
            (checkRequest_large untagged (by omega) other)]
        exact ⟨rfl, close⟩
    · rw [applyEffect_memWrite_error req value tags state state _ (checkRequest_tagged untagged state),
        applyEffect_memWrite_error req value tags other other _ (checkRequest_tagged untagged other)]
      exact ⟨rfl, close⟩
  | memWriteAnnounce request => exact ⟨rfl, close⟩
  | barrier kind => exact ⟨rfl, close⟩
  | cacheOp operation => exact ⟨rfl, close⟩
  | tlbOp operation => exact ⟨rfl, close⟩
  | clockCycle => exact ⟨rfl, close.regs, close.mem, by simp [close.cycles]⟩
  | getCycleCount => exact ⟨close.cycles, close⟩
  | translationStart start => exact ⟨rfl, close⟩
  | translationEnd finish => exact ⟨rfl, close⟩
  | archException exception => exact ⟨rfl, close⟩
  | returnException => exact ⟨rfl, close⟩
  | printMessage message => exact ⟨rfl, close⟩

/-- Every program gives the same result on close states. -/
theorem runSail_close {α : Type} (program : SailM α) :
    ∀ (state other : SailState), Close state other → ResultClose (runSail program state) (runSail program other) := by
  induction program with
  | pure result => intro state other close; exact ⟨rfl, close⟩
  | impure effect next ih =>
    intro state other close
    rcases effect with (error | effect) | choices
    · rw [runSail_error, runSail_error]
      exact ⟨rfl, close⟩
    · rw [runSail_effect, runSail_effect]
      have step := effect_close effect close
      revert step
      cases applyEffect effect state <;> cases applyEffect effect other
      · intro step
        obtain ⟨same, closeMiddle⟩ := step
        subst same
        exact ih _ _ _ closeMiddle
      · intro step; exact step.elim
      · intro step; exact step.elim
      · intro step
        exact step
    · rw [runSail_choice choices next state, runSail_choice choices next other]
      by_cases positive : @LT.lt Nat instLTNat 0 choices
      · rw [dite_eq_left_of_eq_true (eq_true positive), dite_eq_left_of_eq_true (eq_true positive)]
        exact ih ⟨0, positive⟩ state other close
      · rw [dite_eq_right_of_eq_false (eq_false positive), dite_eq_right_of_eq_false (eq_false positive)]
        exact ⟨rfl, close⟩

end Proven.Interpreter
