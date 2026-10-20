import Human.Circuits.Blake2Round.Execution
import Human.Circuits.Keccak.Tables.Controller

namespace Airbender.Blake2Round
open Trace Reference.RiscV.Sail Reference.Sail

/-- x12 after `i` native calls: the three request flags stay fixed, while the
    round bit shifts left and wraps after ten calls. -/
def controlAt (flags : Fin 8) (i : Nat) : Arithmetic.Word :=
  ⟨0, flags.val + 8 * (2 ^ i % 1024)⟩

/-- One uninterrupted extended-BLAKE request span. Public x12 starts with
    round zero and the three caller flags; the pinned caller performs seven
    or ten calls (`common_constants/src/delegation_types/blake2s_with_control.rs`).
    Imported control shifts and initialized matching determine later masks.
    Binding the span to instruction requests remains a separate task. -/
structure CallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (initial : State)
    (cells : List Cell) (flags : Fin 8) : Prop where
  memory : Delegation.MemoryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  controlStart : (Cell.register 12).read initial =
    .ok (BitVec.ofNat 32 ((8 + flags.val) * 65536)) initial
  calls : data.rows.length = if flags.val % 2 = 1 then 7 else 10

/-- Every actual native row has exactly one round bit. This is a conclusion
    of the complete initialized call span, not a per-row caller premise. -/
def CallMasks (data : Delegation.MemoryData p) : Prop :=
  ∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round

/-- Every row uses the three public request flags: reduced rounds, right input
    and compression. These bits come from initialized x12 history and imported
    control equations; the witness cannot choose a different mode per round. -/
def CallModes (data : Delegation.MemoryData p) (flags : Fin 8) : Prop :=
  ∀ row ∈ data.rows, ∀ round : Fin 10,
    let input := Native.input round row.assignment
    input.reducedRounds = decide (flags.val % 2 = 1) ∧
      input.inputIsRight = decide (flags.val / 2 % 2 = 1) ∧
      input.compression = decide (flags.val / 4 = 1)

end Airbender.Blake2Round
