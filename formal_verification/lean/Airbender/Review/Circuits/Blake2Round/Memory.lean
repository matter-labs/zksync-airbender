import Airbender.Review.Helpers.Delegation.Memory
import Airbender.Review.Circuits.Blake2Round.Row

namespace Airbender.Blake2Round.Memory

/-- Historical name for the shared exclusive caller round-mask condition. -/
abbrev RoundMask {p : Nat} (w : Nat → ZMod p) (round : Fin 10) : Prop :=
  Control.RoundMask w round

/-- Public Sail initialization and native matching supply every source word
    and pointer. The pool uses the imported extended-round circuit and current
    modeled XOR table. Native timestamp-offset room and exclusive round masks remain
    explicit until the request interface is connected. -/
structure InterfaceAssumptions [Fact p.Prime] (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell)
    (_input : Row.Input) (_output : Row.Output) (_w : Nat → ZMod p) : Prop where
  accepted : Delegation.MemoryAccepted data
  publicState : Delegation.MemoryInputs data before cells
  families : ∀ row ∈ data.rows, row.family = .blakeRound
  table : data.setup.blakeRound = setupTable
  rounds : ∀ row ∈ data.rows, ∃ round, RoundMask row.assignment round

/-- `Row.Mapping` names the actual controller, pointers, state/message reads
    and native writes. Membership binds that same assignment to the initialized
    history; `round` interprets its exclusive mask as the declared round. -/
structure Mapping (data : Delegation.MemoryData p) (input : Row.Input) (output : Row.Output)
    (w : Nat → ZMod p) : Prop where
  words : Row.Mapping input output w
  member : (⟨.blakeRound, w⟩ : Delegation.Row p) ∈ data.rows
  round : RoundMask w input.round

/-- All native equations, modeled XOR lookups and timestamp queries. The
    conclusion uses the existing project preparation and pinned Clean round. -/
def circuitModel [Fact p.Prime] (data : Delegation.MemoryData p) :
    Verification.CircuitModel Row.Input Row.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (clockConstraints setupTable)
  represents := Mapping data

end Airbender.Blake2Round.Memory
