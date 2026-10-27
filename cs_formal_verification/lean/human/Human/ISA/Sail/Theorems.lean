import Human.ISA.Sail.Airbender
import Human.ISA.Sail.Checks

/-! # What ties our fast spec to Sail (statements only)

Two facts make our own spec `RV.step` (`Human/ISA/RV32.lean`) trustworthy without reviewing it line by line:
1. `DecodeIsSailClaim`: for every word in our encoding table, Sail's own decoder gives the same instruction.
2. `StepIsAirbenderClaim`: our step does exactly what the Airbender machine (`Human/ISA/Sail/Airbender.lean`: Sail's
   `execute` plus the listed changes) does, on everything a program can see.
`Configured` (Airbender behaves as Sail with fixed register values: `misa`, the memory map, …) appears only here, in
the equivalence. `ConfiguredBridgeClaim` ties it to the circuit claims' `Configured` on lean-sail's state.
Proofs: `slop/Slop/Final/ISA/Theorems.lean` (from `slop/Slop/ISA/Equiv/`). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Airbender

/-- Our state `s` and Sail's state `σ` agree on everything a program can see: PC, registers, memory. -/
def AgreeSail (s : RV.State) (σ : SailState) : Prop :=
  Configured σ ∧ σ.regs .PC = s.pc ∧ (∀ i, getReg σ i = s.getReg i) ∧
  (∀ addr : RV.Word, σ.mem addr.toNat = s.mem addr)

/-- … and on the input. -/
def Agree (s : RV.State) (m : Machine) : Prop :=
  AgreeSail s m.sail ∧ m.input = s.input

/-- 1. Sail decodes every word of our table to the same instruction (on any Airbender state). -/
def DecodeIsSailClaim : Prop :=
  ∀ word instr σ, RV.decode word = some instr → Configured σ →
    runSail (ext_decode word) σ = .ok (toSail instr) σ

/-- 2. One step of our spec is one step of the Airbender machine. -/
def StepIsAirbenderClaim : Prop :=
  ∀ s s' m, Agree s m → RV.step s = some s' → ∃ m', step m = some m' ∧ Agree s' m'

/-- The circuit claims' `Configured` (on lean-sail's state, `Human/Helpers/Core/Configuration.lean`) gives this
file's `Configured` on the Sail state it views (`Configuration.SailState.ofState`). -/
def ConfiguredBridgeClaim : Prop :=
  ∀ state : Airbender.Reference.RiscV.Sail.State, Airbender.Reference.RiscV.Sail.Configured state →
    Configured (Airbender.Reference.RiscV.Sail.Configuration.SailState.ofState state)

/-- The checks of `Checks.lean` (Sail's reset, what Airbender overrides Sail rejects, one machine step on
representative words) hold. -/
def MachineChecksClaim : Prop := MachineChecks

/-- `numSteps` steps of the Airbender machine. -/
noncomputable def run : (numSteps : Nat) → Machine → Option Machine
  | 0,     m => some m
  | n + 1, m => (step m).bind (run n)

end Airbender
