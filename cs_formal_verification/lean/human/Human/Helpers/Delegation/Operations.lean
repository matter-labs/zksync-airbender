module
public import Human.Helpers.Delegation.Memory
public import Human.Circuits.Bigint.Tables.Setup
public import Human.Circuits.Blake2G.Tables.Controller
public import Human.Circuits.Blake2Round.Memory
public import Human.Circuits.Keccak.Tables.Setup

@[expose] public section

namespace Airbender.Delegation

/-- The existing modeled tables for all four delegation families. Keccak's
    controller rows stay supplied until physical call scheduling is connected;
    the byte/rotation rows use the same concrete model as its local claims. -/
noncomputable def modeledSetup [Fact p.Prime] (control : Fin 4096 → Vector Nat 6) : Setup p :=
  ⟨Bigint.setupTable, Blake2G.setupTable Blake2G.Control.controllerRows,
    Blake2Round.setupTable, Keccak.setupTable control⟩

/-- Canonical RV32 words for every native read, write and final boundary token.
    These are conclusions of initialized history, shared across families. -/
structure WordBounds (data : MemoryData p) : Prop where
  reads : ∀ row ∈ data.rows, ∀ port ∈ row.ports,
    (Trace.readToken row.assignment port).word.Bounded
  writes : ∀ row ∈ data.rows, ∀ port ∈ row.ports, (row.writeToken port).word.Bounded
  terminal : ∀ token ∈ data.terminal, token.word.Bounded

end Airbender.Delegation
