import Human.ISA.Sail.Airbender

/-! # A circuit row's state, seen as an `RV.State` (DRAFT, B2 pilot)

The circuit claims describe a row's pre-state as a lean-sail state (registers and bytes in hash maps). `view` reads
it as our spec's state: the PC, each register as Sail's instructions read it, every byte of the 2^32 memory (a byte
the state does not hold reads 0, `SailState.ofState`), and the program's input, which the row does not fix (a
parameter: the claims hold for every input). `Same` compares two `RV.State`s on what a program can see. -/

namespace Airbender
open Reference.RiscV.Sail.Configuration

/-- The `RV.State` a lean-sail state stands for, with input `input`. -/
noncomputable def view (state : Reference.RiscV.Sail.State) (input : List RV.Word) : RV.State where
  pc      := (SailState.ofState state).regs .PC
  regFile := fun i => getReg (SailState.ofState state) i
  mem     := fun a => (SailState.ofState state).mem a.toNat
  input   := input

/-- The register number of a Sail register index. -/
def regNumber : SailRV32.regidx → RV.Reg
  | .Regidx r => r

/-- `s` and `t` agree on everything a program can see (x0's stored value is not visible). -/
def Same (s t : RV.State) : Prop :=
  s.pc = t.pc ∧ (∀ i, s.getReg i = t.getReg i) ∧ s.mem = t.mem ∧ s.input = t.input

end Airbender
