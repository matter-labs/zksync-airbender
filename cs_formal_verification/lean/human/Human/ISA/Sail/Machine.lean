/-
# Running the official Sail RISC-V model (RV32) on a simple state.

`SailRV32` is generated from sail-riscv by `sail/regen.sh` (pinned, see `sail/PINS.md`).
Sail's semantics is a program in an effect monad (`SailM`); `runSail` interprets those effects on
`SailState` the same way lean-sail's `interpretSailEffects` does on its hash-map state.

The definitions are the Airbender configuration's (`Human/Helpers/Core/Configuration.lean`: `SailState`,
`SailState.set`, `readBytes`, `writeBytes`, `applyEffect`, `runSail`), made available here under `Human`.
-/
import Human.Helpers.Core.Configuration

namespace Human

export Airbender.Reference.RiscV.Sail.Configuration
  (SailState SailState.set SailState.mk SailState.regs SailState.mem SailStateM readBytes writeBytes applyEffect runSail)

end Human

namespace Airbender.Reference.RiscV.Sail.Configuration

/-- The Sail state a lean-sail state (the circuit claims' `State`) stands for: its registers and memory bytes, with a
register it does not hold at its reset value and a byte it does not hold 0 (lean-sail's interpreter fails on reading
either, so a successful run never sees these defaults). -/
noncomputable def SailState.ofState (state : Airbender.Reference.RiscV.Sail.State) : SailState where
  regs r := (state.regs.get? r).getD (resetState.regs r)
  mem a := (state.mem.get? a).getD 0

end Airbender.Reference.RiscV.Sail.Configuration
