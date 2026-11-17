import Human.ISA.Sail.Machine

/-! # `runSail` and lean-sail's sequential interpreter

The Sail claims run the generated model with `runSail` (`Human/Helpers/Core/Configuration.lean`). lean-sail's own
interpreter `interpretSailEffects` keeps registers and memory in hash maps, which the kernel cannot evaluate
(`sail/README.md`). The claim below relates the two interpreters on every program that does not read the cycle
counter. -/

open Sail Sail.ArchSem SailRV32 Human

namespace Airbender

/-- lean-sail's sequential state for the generated RV32 registers. -/
abbrev SequentialSailState := SequentialState RegisterType

/-- The lean-sail state holds a part of the registers and bytes of a `SailState`, with the same values. -/
structure SequentialAgrees (state : SailState) (sequential : SequentialSailState) : Prop where
  /-- Each register in the lean-sail map has its `SailState` value. -/
  regs : ∀ register value, sequential.regs.get? register = some value → state.regs register = value
  /-- Each byte in the lean-sail map has its `SailState` value. -/
  mem : ∀ address byte, sequential.mem.get? address = some byte → state.mem address = byte

/-- The lean-sail errors for a register or byte that is not in its map, or for a tagged memory request. -/
def MissingData : Sail.Error exception → Prop
  | .Unreachable => True
  | .OutOfMemoryRange _ => True
  | .Assertion message => message = "Tagged memory not supported"
  | _ => False

/-- The program never reads the cycle counter. `SailState` has no cycle counter. The generated RV32 model has no
    `get_cycle_count` call. -/
inductive NoCycleRead {α : Type} : SailM α → Prop where
  /-- A returned value reads nothing. -/
  | pure (value : α) : NoCycleRead (.pure value)
  /-- An effect other than the cycle-counter read, followed by a continuation with no such read. -/
  | impure (effect : (Except (Sail.Error exception) InstructionEffect) ⊕ FinChoice)
      (next : Effect.ret effect → SailM α) (other : effect ≠ .inl (.ok .getCycleCount))
      (rest : ∀ result, NoCycleRead (next result)) : NoCycleRead (.impure effect next)

/-- `runSail` agrees with lean-sail's `interpretSailEffects` on every program that does not read the cycle counter.
    The lean-sail state holds a part of the registers and bytes, with the same values.
    A successful lean-sail run gives the same value in `runSail`. A successful `runSail` run gives the same value
    in lean-sail, or lean-sail stops because a register or byte is not in its map or a memory request is tagged.
    The final states agree in the same way. -/
def RunSailSimulationClaim : Prop :=
  ∀ {α : Type} (program : SailM α) (state : SailState) (sequential : SequentialSailState),
    NoCycleRead program → SequentialAgrees state sequential →
    (∀ value sequential', (interpretSailEffects program).run sequential = .ok value sequential' →
      ∃ state', runSail program state = .ok value state' ∧ SequentialAgrees state' sequential') ∧
    (∀ value state', runSail program state = .ok value state' →
      (∃ sequential', (interpretSailEffects program).run sequential = .ok value sequential' ∧
        SequentialAgrees state' sequential') ∨
      ∃ error sequential', (interpretSailEffects program).run sequential = .error error sequential' ∧
        MissingData error)

/-- A register write and read meet the premises, and lean-sail runs the program to completion. -/
def RunSailSimulationSatisfiableClaim : Prop :=
  ∃ (program : SailM (RegisterType .PC)) (state : SailState) (sequential : SequentialSailState)
    (value : RegisterType .PC) (sequential' : SequentialSailState),
    NoCycleRead program ∧ SequentialAgrees state sequential ∧
    (interpretSailEffects program).run sequential = .ok value sequential'

end Airbender
