import Human.Helpers.Delegation.Memory
import Human.Circuits.Keccak.Tables.Setup

namespace Airbender.Keccak.Memory

/-- Public initialization for an active Keccak pool. `publicState` reads the
    initial Sail registers/RAM and lists native timestamp-offset room. The setup is
    the current modeled table; controller rows remain a supplied interface.
    `active` identifies real calls: inactive padding writes are not constrained
    to preserve words by this local artifact. No word range or read is assumed. -/
structure Inputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell)
    (control : Fin 4096 → Vector Nat 6) : Prop where
  publicState : Delegation.MemoryInputs data before cells
  families : ∀ row ∈ data.rows, row.family = .keccak
  table : data.setup.keccak = setupTable control
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1

end Airbender.Keccak.Memory
