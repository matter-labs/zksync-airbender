import Airbender.Review.Helpers.UnifiedReduced.Windows

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Original Sail instructions that write a public constant from x0 or a U-immediate. -/
inductive ControlLiteral where
  | addi (immediate : BitVec 12)
  | lui (immediate : BitVec 20)

def ControlLiteral.instruction (literal : ControlLiteral) (register : BitVec 5) : SailRV32.instruction :=
  match literal with
  | .addi immediate => .ITYPE (immediate, .Regidx 0, .Regidx register, .ADDI)
  | .lui immediate => .UTYPE (immediate, .Regidx register, .LUI)

/-- The same original Sail sign extension and U-immediate packing used by decoding. -/
def ControlLiteral.value : ControlLiteral → BitVec 32
  | .addi immediate => SailRV32.Functions.sign_extend (m := 32) immediate
  | .lui immediate => immediate ++ (0 : BitVec 12)

/-- Public preparation registry and its final cycle. Native matching identifies
    the final preparation row; no row selector, control read or write is supplied. -/
structure ControlPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat) (register : BitVec 5) (literal : ControlLiteral) : Prop where
  /-- The ordinary public instruction registry prepares this constant. -/
  program : ∀ entry ∈ program, entry.instruction = literal.instruction register
  /-- Workers may precede preparation, but none writes in its final cycle. -/
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  /-- At least one complete preparation cycle follows the public initial clock. -/
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  /-- The cut lies within the accepted native machine path. -/
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- The actual control token retains the final preparation write's timestamp. -/
def PreparedControl (tokens : List (MemoryToken p)) (state : State) (cut : Nat)
    (register : BitVec 5) (literal : ControlLiteral) : Prop :=
  (Cell.register register).read state = .ok literal.value state ∧
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧ token.word.toBitVec = literal.value

end Airbender.UnifiedReduced.Caller
