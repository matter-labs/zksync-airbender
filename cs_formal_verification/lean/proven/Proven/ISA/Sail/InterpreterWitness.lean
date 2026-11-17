import Proven.ISA.Sail.InterpreterMachine
import Proven.ISA.Equiv.WholeRun

/-! Agreeing lean-sail states exist: one map entry for every register and for every byte below `requestReach`. -/

open Sail Sail.ArchSem SailRV32 Human

namespace Proven.Interpreter
open Airbender

/-- The number of generated RV32 registers. -/
def registerCount : Nat := 213

/-- Every generated register has an index below `registerCount`. -/
theorem register_listed (register : Register) :
    register ∈ (List.range registerCount).map Register.ofNat :=
  List.mem_map.mpr ⟨register.ctorIdx, List.mem_range.mpr (by unfold registerCount; cases register <;> decide),
    by cases register <;> rfl⟩

/-- Insert the value of every key of a list. Irreducible, so that unification never evaluates the key list. -/
@[irreducible] def insertAll {α : Type} [BEq α] [LawfulBEq α] [Hashable α] {β : α → Type} (values : (key : α) → β key)
    (keys : List α) (map : Std.ExtDHashMap α β) : Std.ExtDHashMap α β :=
  keys.foldl (fun map key => map.insert key (values key)) map

/-- Insert the value of every key of a list. Irreducible, so that unification never evaluates the key list. -/
@[irreducible] def insertAllBytes {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] (values : α → β) (keys : List α)
    (map : Std.ExtHashMap α β) : Std.ExtHashMap α β :=
  keys.foldl (fun map key => map.insert key (values key)) map

/-- `insertAll` of no keys keeps the map. -/
theorem insertAll_nil {α : Type} [BEq α] [LawfulBEq α] [Hashable α] {β : α → Type} (values : (key : α) → β key)
    (map : Std.ExtDHashMap α β) : insertAll values [] map = map := by
  unfold insertAll
  rfl

/-- `insertAll` inserts the first key, then the rest. -/
theorem insertAll_cons {α : Type} [BEq α] [LawfulBEq α] [Hashable α] {β : α → Type} (values : (key : α) → β key)
    (first : α) (rest : List α) (map : Std.ExtDHashMap α β) :
    insertAll values (first :: rest) map = insertAll values rest (map.insert first (values first)) := by
  unfold insertAll
  rfl

/-- `insertAllBytes` of no keys keeps the map. -/
theorem insertAllBytes_nil {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] (values : α → β)
    (map : Std.ExtHashMap α β) : insertAllBytes values [] map = map := by
  unfold insertAllBytes
  rfl

/-- `insertAllBytes` inserts the first key, then the rest. -/
theorem insertAllBytes_cons {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] (values : α → β) (first : α)
    (rest : List α) (map : Std.ExtHashMap α β) :
    insertAllBytes values (first :: rest) map = insertAllBytes values rest (map.insert first (values first)) := by
  unfold insertAllBytes
  rfl

/-- Inserts of other keys keep the value of a key. -/
theorem get?_insertAll_other {α : Type} [BEq α] [LawfulBEq α] [Hashable α] {β : α → Type}
    (values : (key : α) → β key) (key : α) (value : β key) (keys : List α) (absent : key ∉ keys) :
    ∀ map : Std.ExtDHashMap α β, map.get? key = some value → (insertAll values keys map).get? key = some value := by
  induction keys with
  | nil => intro map present; rw [insertAll_nil]; exact present
  | cons first rest ih =>
    intro map present
    have different : first ≠ key := fun same => absent (same ▸ List.mem_cons_self)
    rw [insertAll_cons]
    apply ih (fun later => absent (List.mem_cons_of_mem _ later))
    rw [Std.ExtDHashMap.get?_insert, dite_eq_right_of_eq_false (by simpa using different)]
    exact present

/-- A listed key holds its value after `insertAll`. -/
theorem get?_insertAll {α : Type} [BEq α] [LawfulBEq α] [Hashable α] {β : α → Type}
    (values : (key : α) → β key) (keys : List α) :
    ∀ (map : Std.ExtDHashMap α β) (key : α), key ∈ keys → (insertAll values keys map).get? key = some (values key) := by
  induction keys with
  | nil => intro map key listed; cases listed
  | cons first rest ih =>
    intro map key listed
    rw [insertAll_cons]
    by_cases inside : key ∈ rest
    · exact ih _ key inside
    · have same : first = key := by
        rcases List.mem_cons.mp listed with same | later
        · exact same.symm
        · exact absurd later inside
      subst same
      exact get?_insertAll_other values first _ rest inside _ Std.ExtDHashMap.get?_insert_self

/-- Inserts of other keys keep the value of a key. -/
theorem get?_insertAllBytes_other {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] (values : α → β) (key : α)
    (value : β) (keys : List α) (absent : key ∉ keys) :
    ∀ map : Std.ExtHashMap α β, map.get? key = some value → (insertAllBytes values keys map).get? key = some value := by
  induction keys with
  | nil => intro map present; rw [insertAllBytes_nil]; exact present
  | cons first rest ih =>
    intro map present
    have different : first ≠ key := fun same => absent (same ▸ List.mem_cons_self)
    rw [insertAllBytes_cons]
    apply ih (fun later => absent (List.mem_cons_of_mem _ later))
    rw [Std.ExtHashMap.get?_eq_getElem?] at present ⊢
    rw [Std.ExtHashMap.getElem?_insert]
    simp [different, present]

/-- A listed key holds its value after `insertAllBytes`. -/
theorem get?_insertAllBytes {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] (values : α → β) (keys : List α) :
    ∀ (map : Std.ExtHashMap α β) (key : α), key ∈ keys →
      (insertAllBytes values keys map).get? key = some (values key) := by
  induction keys with
  | nil => intro map key listed; cases listed
  | cons first rest ih =>
    intro map key listed
    rw [insertAllBytes_cons]
    by_cases inside : key ∈ rest
    · exact ih _ key inside
    · have same : first = key := by
        rcases List.mem_cons.mp listed with same | later
        · exact same.symm
        · exact absurd later inside
      subst same
      exact get?_insertAllBytes_other values first _ rest inside _ (by simp [Std.ExtHashMap.get?_eq_getElem?])

/-- The lean-sail state with every register and every byte below `requestReach` of `state`. -/
noncomputable def fullSequential (state : SailState) : SequentialSailState where
  regs := insertAll state.regs ((List.range registerCount).map Register.ofNat) ∅
  mem := insertAllBytes state.mem (List.range requestReach) ∅
  tags := ()
  cycleCount := state.cycles
  sailOutput := #[]

/-- The full lean-sail state holds every register. -/
theorem full_registers (state : SailState) (register : Register) :
    (fullSequential state).regs.get? register = some (state.regs register) := by
  unfold fullSequential
  exact get?_insertAll state.regs ((List.range registerCount).map Register.ofNat) ∅ register (register_listed register)

/-- The full lean-sail state holds every byte below `requestReach`. -/
theorem full_bytes (state : SailState) (address : Nat) (reach : address < requestReach) :
    (fullSequential state).mem.get? address = some (state.mem address) := by
  unfold fullSequential
  exact get?_insertAllBytes state.mem (List.range requestReach) ∅ address (List.mem_range.mpr reach)

/-- The full lean-sail state of `state` agrees with it. -/
theorem full_agrees (state : SailState) : SequentialAgrees state (fullSequential state) :=
  ⟨full_registers state, full_bytes state, rfl⟩

/-- Write the PC, then read it. -/
def writeReadPC : SailM (RegisterType .PC) :=
  .impure (.inl (.ok (.regWrite .PC none (4 : BitVec 32)))) fun _ =>
    .impure (.inl (.ok (.regRead .PC none))) .pure

/-- `runSail` writes and reads the PC. -/
theorem run_writeReadPC (state : SailState) :
    runSail writeReadPC state = .ok (4 : BitVec 32) (state.set .PC (4 : BitVec 32)) := by
  unfold writeReadPC
  rw [runSail_effect]
  change runSail (.impure (.inl (.ok (.regRead .PC none))) .pure) (state.set .PC (4 : BitVec 32)) = _
  rw [runSail_effect]
  change EStateM.Result.ok ((state.set .PC (4 : BitVec 32)).regs .PC) (state.set .PC (4 : BitVec 32)) = _
  simp [SailState.set]

/-- A register write and read run under `runSail` from a state with an agreeing lean-sail state. -/
theorem run_sail_simulation_satisfiable : RunSailSimulationSatisfiableClaim :=
  ⟨writeReadPC, resetState, _, fullSequential resetState, _, full_agrees resetState, run_writeReadPC resetState⟩

/-- The configured machine that runs one step has an agreeing lean-sail state. -/
theorem machine_run_is_sequential_satisfiable : MachineRunIsSequentialSatisfiableClaim := by
  obtain ⟨state, after, machine, agreement, stepped⟩ := Proven.Equiv.NonVacuous.step_assumptions
  obtain ⟨machine', run, _⟩ := Proven.Equiv.run_is_airbender 1 state after machine agreement
    (by simp only [RV.run, stepped, Option.bind_some])
  exact ⟨1, machine, machine', fullSequential machine.sail, le_refl 1, full_agrees machine.sail, run⟩

end Proven.Interpreter
