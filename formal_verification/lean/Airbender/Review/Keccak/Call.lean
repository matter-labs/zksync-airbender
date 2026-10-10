import Airbender.Review.Delegation.Memory

namespace Airbender.Keccak
open Trace Reference.RiscV.Sail Reference.Sail

/-- Public boundary for one uninterrupted Keccak request span. The pinned caller
    performs 649 calls with x10 initially zero (`common_constants/src/delegation_types/keccak_special5.rs`).
    Shared initialized matching proves every later control read. Connecting this
    span to the calling instruction trace remains the request-binding task. -/
structure CallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (initial : State)
    (cells : List Cell) : Prop where
  memory : Delegation.MemoryInputs data initial cells
  controlCell : Cell.register 10 ∈ cells
  controlStart : (Cell.register 10).read initial = .ok 0 initial
  /-- This span contains the active calls of this one request. -/
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  calls : data.rows.length = 649

/-- The declared final x10 token is the caller's completion value 1544. This
    is a proved result, never an assumed response or per-row control sequence. -/
def CallControl (data : Delegation.MemoryData p) : Prop :=
  ∃ sink ∈ data.terminal, sink.address = (Cell.register 10).addressCode ∧
    sink.word = Arithmetic.Word.ofBitVec 1544

end Airbender.Keccak
