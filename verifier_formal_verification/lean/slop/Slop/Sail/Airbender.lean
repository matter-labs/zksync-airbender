/-
# Legacy: the first Sail route (whole `try_step`, with `minstret`), used by the old PoC files
(`Config`, `Contract`, `StepDemo`, `StepAddi`). The machine itself is `HumanSail/Airbender.lean`.
-/
import HumanSail.Airbender

open Sail SailRV32 SailRV32.Functions

namespace Human
export Airbender (misa region RAM_START RAM_END memoryMap sailResetRun resetState writtenByProgram Configured)

/-- RV32IM instructions (Sail's decoder already rejects RV64-only forms such as `ld`). -/
def Supported : instruction → Bool
  | .UTYPE _ | .JAL _ | .JALR _ | .BTYPE _ | .ITYPE _ | .SHIFTIOP _ | .RTYPE _
  | .LOAD _ | .STORE _ | .MUL _ | .DIV _ | .REM _ => true
  | _ => false

/-- Airbender's CSRs, accessed with `csrrw` only: 0x7c0 (input/output oracle), 0x7c7, 0x7ca (precompiles).
For now they do nothing (the instruction is skipped). -/
def NopCSR : instruction → Bool
  | .CSRReg (csr, _, _, .CSRRW) => csr == 0x7c0 || csr == 0x7c7 || csr == 0x7ca
  | _ => false

/-- The instruction at the PC, fetched and decoded by Sail. -/
noncomputable def current (s : SailState) : Option instruction :=
  match runSail (fetch ()) s with
  | .ok (.F_Base w) _ => match runSail (ext_decode w) s with | .ok i _ => some i | _ => none
  | _ => none

/-- One step: a supported instruction is executed by Sail's `try_step`; an Airbender CSR is skipped;
anything else stops the machine (`none`). -/
noncomputable def step (s : SailState) : Option SailState :=
  match current s with
  | some i =>
    if Supported i then
      match runSail (try_step 0 false) s with
      | .ok false s' => some s'
      | _ => none
    else if NopCSR i then
      let pc := s.regs .PC + 4
      some (((s.set .PC pc).set .nextPC pc).set .minstret (s.regs .minstret + 1))
    else none
  | none => none

/-- `s` executes one instruction that retires normally (no trap, no fault, not stopped). -/
def Retired (s s' : SailState) : Prop :=
  step s = some s' ∧ s'.regs .minstret = s.regs .minstret + 1

/-- `n` consecutive retired instructions lead from `s` to `s'`. -/
inductive Runs : Nat → SailState → SailState → Prop
  | zero : Runs 0 s s
  | succ : Retired s s₁ → Runs n s₁ s' → Runs (n+1) s s'

end Human
