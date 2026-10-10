import Airbender.Review.Delegation.Memory
import Airbender.Review.Bigint.Tables
import Airbender.Review.Blake2G.Control
import Airbender.Review.Blake2Round.Memory
import Airbender.Review.Keccak.Tables

namespace Airbender.Delegation

/-- The existing modeled tables for all four delegation families. Keccak's
    controller rows stay supplied until physical call scheduling is connected;
    the byte/rotation rows use the same concrete model as its local claims. -/
def modeledSetup [Fact p.Prime] (control : Fin 4096 → Vector Nat 6) : Setup p :=
  ⟨Bigint.setupTable, Blake2G.setupTable Blake2G.Control.controllerRows,
    Blake2Round.setupTable, Keccak.setupTable control⟩

/-- Public inputs for an initialized pool mixing any delegation families.
    Memory matching and imported constraints supply the reads and bounds.
    `rounds` and `keccakActive` are caller/padding conditions still awaiting
    request binding, not arithmetic results. No bigint opcode restriction is
    added here: its checked local ABI mismatch stays visible. -/
structure OperationInputs [Fact p.Prime] (data : MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell)
    (control : Fin 4096 → Vector Nat 6) : Prop where
  publicState : MemoryInputs data before cells
  tables : data.setup = modeledSetup control
  rounds : ∀ row ∈ data.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round
  keccakActive : ∀ row ∈ data.rows, row.family = .keccak →
    row.assignment Keccak.Variables.execute = 1

/-- Canonical RV32 words for every native read, write and final boundary token.
    These are conclusions of initialized history, shared across families. -/
structure WordBounds (data : MemoryData p) : Prop where
  reads : ∀ row ∈ data.rows, ∀ port ∈ row.ports,
    (Trace.readToken row.assignment port).word.Bounded
  writes : ∀ row ∈ data.rows, ∀ port ∈ row.ports, (row.writeToken port).word.Bounded
  terminal : ∀ token ∈ data.terminal, token.word.Bounded

end Airbender.Delegation
