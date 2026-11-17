import Human.ISA.Sail.WholeRun

/-! # `runSail` and lean-sail's sequential interpreter

The Sail claims run the generated model with `runSail` (`Human/Helpers/Core/Configuration.lean`). lean-sail's own
interpreter `interpretSailEffects` keeps registers and memory in hash maps, which the kernel cannot evaluate
(`sail/README.md`). The claims below carry every successful `runSail` run, and every finite machine run, to
lean-sail's interpreter. Each `…FromNativeSailClaim` target gives a finite machine run, so it also gives a run of the
same length under lean-sail's interpreter. -/

open Sail Sail.ArchSem SailRV32 Human

namespace Airbender

/-- lean-sail's sequential state for the generated RV32 registers. -/
abbrev SequentialSailState := SequentialState RegisterType

/-- The bytes that a memory request can reach: a 34-bit address and at most `maxRequestBytes` bytes. -/
def requestReach : Nat := 2 ^ 34 + Reference.RiscV.Sail.Configuration.maxRequestBytes

/-- The lean-sail state holds every register and every byte that a memory request can reach, with the values of the
    `SailState`. The cycle counters are equal. -/
structure SequentialAgrees (state : SailState) (sequential : SequentialSailState) : Prop where
  /-- Each register has its `SailState` value. -/
  regs : ∀ register, sequential.regs.get? register = some (state.regs register)
  /-- Each byte that a memory request can reach has its `SailState` value. -/
  mem : ∀ address, address < requestReach → sequential.mem.get? address = some (state.mem address)
  /-- The cycle counters are equal. -/
  cycles : sequential.cycleCount = state.cycles

/-- The `SailState` that a lean-sail state describes. A register or byte that is not in its maps has its reset
    value or zero. -/
noncomputable def SequentialSailState.view (sequential : SequentialSailState) : SailState where
  regs register := (sequential.regs.get? register).getD (resetState.regs register)
  mem address := (sequential.mem.get? address).getD 0
  cycles := sequential.cycleCount

/-- The lean-sail state with the register and byte values of `state` at every key that it holds. -/
noncomputable def SequentialSailState.update (sequential : SequentialSailState) (state : SailState) :
    SequentialSailState :=
  { sequential with
    regs := sequential.regs.map fun register _ => state.regs register
    mem := sequential.mem.map fun address _ => state.mem address
    cycleCount := state.cycles }

/-- The Airbender machine on lean-sail's sequential state. -/
structure SequentialMachine where
  /-- lean-sail's registers, memory and cycle counter. -/
  sail : SequentialSailState
  /-- Architectural RAM values below the Sail RAM boundary. -/
  shadow : Shadow
  /-- Public input words that the machine has not read. -/
  input : List (BitVec 32)

/-- One step of the machine with lean-sail's interpreter. A Sail instruction runs under `interpretSailEffects`.
    A delegation call is Airbender's own operation (`delegation`) on the state that the lean-sail state describes. -/
noncomputable def SequentialMachine.step (machine : SequentialMachine) : Option SequentialMachine :=
  match delegation machine.sail.view machine.shadow with
  | some result => result.map fun (state, shadow) => ⟨machine.sail.update state, shadow, machine.input⟩
  | none =>
    match (interpretSailEffects (sailStep (machine.input.headD 0))).run machine.sail, machine.input with
    | .ok (some false) sequential, input => some ⟨sequential, machine.shadow, input⟩
    | .ok (some true) sequential, _ :: rest => some ⟨sequential, machine.shadow, rest⟩
    | _, _ => none

/-- Execute exactly the given number of machine steps with lean-sail's interpreter. -/
noncomputable def SequentialMachine.run : Nat → SequentialMachine → Option SequentialMachine
  | 0, machine => some machine
  | n + 1, machine => machine.step.bind (SequentialMachine.run n)

/-- Every successful `runSail` run of a Sail program is a successful run under lean-sail's `interpretSailEffects`
    from every agreeing lean-sail state. The value is the same and the final states agree. -/
def RunSailSimulationClaim : Prop :=
  ∀ {α : Type} (program : SailM α) (state state' : SailState) (sequential : SequentialSailState) (value : α),
    SequentialAgrees state sequential → runSail program state = .ok value state' →
    ∃ sequential', (interpretSailEffects program).run sequential = .ok value sequential' ∧
      SequentialAgrees state' sequential'

/-- A register write and read run under `runSail` from a state that has an agreeing lean-sail state. -/
def RunSailSimulationSatisfiableClaim : Prop :=
  ∃ (program : SailM (RegisterType .PC)) (state state' : SailState) (sequential : SequentialSailState)
    (value : RegisterType .PC),
    SequentialAgrees state sequential ∧ runSail program state = .ok value state'

/-- Every finite run of the Airbender machine is a run of the same length with lean-sail's interpreter, from every
    agreeing lean-sail state. The final states agree. The shadow RAM and the input are the same. -/
def MachineRunIsSequentialClaim : Prop :=
  ∀ (n : Nat) (machine machine' : Machine) (sequential : SequentialSailState),
    SequentialAgrees machine.sail sequential → Machine.run n machine = some machine' →
    ∃ sequential', SequentialMachine.run n ⟨sequential, machine.shadow, machine.input⟩ =
        some ⟨sequential', machine'.shadow, machine'.input⟩ ∧ SequentialAgrees machine'.sail sequential'

/-- A machine that runs at least one step has an agreeing lean-sail state. -/
def MachineRunIsSequentialSatisfiableClaim : Prop :=
  ∃ (n : Nat) (machine machine' : Machine) (sequential : SequentialSailState),
    1 ≤ n ∧ SequentialAgrees machine.sail sequential ∧ Machine.run n machine = some machine'

end Airbender
