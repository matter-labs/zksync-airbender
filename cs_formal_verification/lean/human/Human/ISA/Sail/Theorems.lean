import Human.ISA.Sail.Airbender
import Human.ISA.Sail.Checks

/-! # What ties our fast spec to Sail (statements only)

Two facts make our own spec `RV.step` (`Human/ISA/RV32.lean`) trustworthy without reviewing it line by line:
1. `DecodeIsSailClaim`: for every word in our encoding table, Sail's own decoder gives the same instruction.
2. `StepIsAirbenderClaim`: our step does exactly what the Airbender machine (`Human/ISA/Sail/Airbender.lean`: Sail's
   `execute` plus the listed changes) does, on everything a program can see.
`Configured` (Airbender behaves as Sail with fixed register values: `misa`, the memory map, …) appears only here, in
the equivalence.
Proofs: `slop/Slop/Final/ISA/Theorems.lean` (from `slop/Slop/ISA/Equiv/`). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Airbender

/-- Our state `s` and Sail's state `σ` agree on everything a program can see: PC, registers, memory (Sail's memory is
what a LOAD sees: the ROM image below `ROM_END`, RAM above). -/
def AgreeSail (s : RV.State) (σ : SailState) : Prop :=
  Configured σ ∧ σ.regs .PC = s.pc ∧ (∀ i, getReg σ i = s.getReg i) ∧
  (∀ addr : RV.Word, σ.mem addr.toNat = s.loadView addr)

/-- … on the shadow RAM (RAM below `ROM_END`, which only delegations reach) and on the input. -/
def Agree (s : RV.State) (m : Machine) : Prop :=
  AgreeSail s m.sail ∧ (∀ addr : RV.Word, addr.toNat < RV.ROM_END → m.shadow addr = s.mem addr) ∧
    m.input = s.input

/-- 1. Sail decodes every word of our table to the same instruction (on any Airbender state). -/
def DecodeIsSailClaim : Prop :=
  ∀ word instr σ, RV.decode word = some instr → Configured σ →
    runSail (ext_decode word) σ = .ok (toSail instr) σ

/-- 2. One step of our spec is one step of the Airbender machine. -/
def StepIsAirbenderClaim : Prop :=
  ∀ s s' m, Agree s m → RV.step s = some s' → ∃ m', step m = some m' ∧ Agree s' m'

/-- The checks of `Checks.lean` (Sail's reset, what Airbender overrides Sail rejects, one machine step on
representative words) hold. -/
def MachineChecksClaim : Prop := MachineChecks

end Airbender
