import Airbender.Review.UnifiedReduced.MixedWindows

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

/-- Public preparation registry and first-span scope. Native matching identifies
    the final preparation row; no row selector, control read or write is supplied. -/
structure ControlPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat) (register : BitVec 5) (literal : ControlLiteral) : Prop where
  /-- The ordinary public instruction registry prepares this constant. -/
  program : ∀ entry ∈ program, entry.instruction = literal.instruction register
  /-- Existing first-span ABI: earlier workers, including surplus rows, are absent. -/
  prefixScope : data.workers.prefixRows cut = []
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

/-- Public initialization and accepted ordinary writes reach an actual prepared
    cut state. This is control preparation and memory transport, not whole retirement. -/
def PreparedBoundaryExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (cut : Nat) (register : BitVec 5) (literal : ControlLiteral) : Prop :=
  ∃ (tokens : List (MemoryToken p)) (events : List MemoryAccess) (atCut : State),
    events.Perm ((data.prefixSteps cut).map transferEvent) ∧
    SailHistory cells events before atCut ∧ NativeBoundary tokens atCut cells ∧
    PreparedControl tokens atCut cut register literal

end Airbender.UnifiedReduced.Caller
