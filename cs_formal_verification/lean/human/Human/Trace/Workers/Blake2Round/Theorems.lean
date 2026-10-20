import Human.Circuits.AddSub.Reference
import Human.Circuits.Bigint.Additive
import Human.Circuits.Bigint.Equality
import Human.Circuits.Bigint.Multiplication
import Human.Circuits.Blake2G.State
import Human.Circuits.Keccak.Chi
import Human.Circuits.Keccak.Iota
import Human.Helpers.Core.BabyBearPrime
import Human.Trace.Workers.Blake2Round.BoundaryCall
import Human.Trace.Workers.Blake2Round.Windows

-- The statements proven in slop/Slop/Final/Trace/Workers/Blake2Round/Theorems.lean (checked by verify.sh).

namespace Airbender.Blake2Round.Native

/-- The complete extended row matches its existing preparation, Clean eight-G
    round, chaining, control and address references on actual Sail port values.
    Other delegation families may share the history; source/pointer ranges and
    reads are derived internally. The exclusive round mask remains a visible
    caller condition in `OperationInputs`; full compression/caller ABI is separate. -/
def OperationExecutionClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.OperationInputs data before cells control) (aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeRound →
        ∃ round, Memory.RoundMask row.assignment round ∧ Row.spec (input round row.assignment) (output row.assignment)

/-- The complete seven or ten round compression reaches its reference output in
    actual Sail RAM. `WordMapping` identifies successful initial/final block
    reads; all word bounds and intermediate reads are proved from matching.
    `CallInputs` retains the public request span and modeled-table boundary. -/
def CompressionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {flags : Fin 8} (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells flags) (aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : Reference.RiscV.Sail.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.WordMapping initial after statePointer messagePointer input output message ∧
        Delegation.TraceMapping data initial after cells ∧
        output = Compression.run flags input message

/-- The complete extended-BLAKE reference binds actual boundary reads and the
    final Sail state with retained seed timestamps. Round masks, request modes
    and intermediate states follow from accepted history and the public ABI. -/
def CompressionBoundarySoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {flags : Fin 8} (accepted : Delegation.MemoryAccepted data) (inputs : NativeCallInputs data initial cells flags) (aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : Reference.RiscV.Sail.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.WordMapping initial after statePointer messagePointer input output message ∧
        Delegation.TraceMapping data initial after cells ∧
        output = Compression.run flags input message

/-- The first complete compression reaches its reference on actual cut states
    from a retained native boundary. Initialized history derives every round mask
    within the explicit ten-position pool and every intermediate value. -/
def WindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {flags : Fin 8} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data) (inputs : WindowInputs data before cells flags lower upper) (aligned : ∀ cell ∈ cells, cell.Aligned),
    (Delegation.Caller.HashSpan.blakeRound flags).WindowResult data before cells lower upper

end Airbender.Blake2Round.Native
