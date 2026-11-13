import Human.ISA.Sail.Theorems
import Human.Trace.Machine.Theorems

open Sail SailRV32 SailRV32.Functions Human
namespace Airbender

/-- Execute exactly the given number of Airbender machine instructions. A failed step has no result. -/
noncomputable def Machine.run : Nat → Machine → Option Machine
  | 0, machine => some machine
  | n + 1, machine => (step machine).bind (Machine.run n)

/-- Read an architectural register or a word of RAM. Shadow RAM supplies addresses below the ROM boundary. -/
noncomputable def Machine.readCell (machine : Machine) (cell : Trace.Cell) : Option RV.Word :=
  match cell with
  | .register index => some (getReg machine.sail index)
  | .ram address =>
    if RV.readable address 4 then some (RV.read (ramView machine.sail machine.shadow) address 4) else none

/-- Every finite RV execution has an agreeing Airbender machine execution of the same length. -/
def RunIsAirbenderClaim : Prop :=
  ∀ n s s' machine, Agree s machine → RV.run n s = some s' →
    ∃ machine', Machine.run n machine = some machine' ∧ Agree s' machine'

/-- An agreeing configured machine exists for every initial boot state. ROM, RAM and input are arbitrary. -/
def AgreeExistsClaim : Prop :=
  ∀ s : RV.State, ∃ machine, Agree s machine

/-- The finite run premise can be met by agreeing states. -/
def RunIsAirbenderSatisfiableClaim : Prop :=
  ∃ n s s' machine, Agree s machine ∧ RV.run n s = some s'

/-- The public boot-state premises can be met. -/
def AgreeExistsSatisfiableClaim : Prop :=
  ∃ s machine, Agree s machine

/-- A supported ROM fetch retains the configured Sail registers used by the decoder theorem. -/
def FetchKeepsConfiguredClaim : Prop :=
  ∀ (state : SailState) word instruction result state',
    Configured state → (state.regs .PC).toNat % 4 = 0 →
    (state.regs .PC).toNat + 4 ≤ RAM_START →
    readBytes state.mem (state.regs .PC).toNat 4 = word →
    RV.decode word = some instruction →
    runSail (fetch ()) state = .ok result state' → Configured state'


/-- A supported aligned ROM fetch has all premises of the fetch configuration claim. -/
def FetchKeepsConfiguredSatisfiableClaim : Prop :=
  ∃ (state : SailState) (word : RV.Word) (instruction : RV.Instr) (result : _) (state' : SailState),
    Configured state ∧ (state.regs .PC).toNat % 4 = 0 ∧
    (state.regs .PC).toNat + 4 ≤ RAM_START ∧
    readBytes state.mem (state.regs .PC).toNat 4 = word ∧
    RV.decode word = some instruction ∧ runSail (fetch ()) state = .ok result state'

namespace Trace
/-- A configured Airbender machine runs from the public initial state to every accepted terminal value. -/
def SailRealizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [_root_.Fact p.Prime]
    (trace : Data p Kind) (initial : RV.State) (cells : List Cell) : Prop :=
  ∃ start finish n, Agree initial start ∧ Machine.run n start = some finish ∧
    finish.sail.regs .PC = trace.terminal.word.toBitVec ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      finish.readCell cell = some sink.word.toBitVec
end Trace
end Airbender
