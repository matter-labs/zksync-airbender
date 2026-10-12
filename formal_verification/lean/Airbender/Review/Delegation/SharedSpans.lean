import Airbender.Review.Delegation.WorkerProjection
import Airbender.Review.Blake2G.WorkVector
import Airbender.Review.Blake2Round.Compression
import Airbender.Review.Keccak.Permutation

namespace Airbender.Delegation.Caller
open Trace Reference.RiscV.Sail

/-- The existing pinned hash-call protocols: G work-vector update, extended
    BLAKE compression or Keccak permutation. Flags are public caller inputs. -/
inductive HashSpan where
  | blakeG (reduced : Bool)
  | blakeRound (flags : Fin 8)
  | keccak

def HashSpan.family : HashSpan → Family
  | .blakeG _ => .blakeG
  | .blakeRound _ => .blakeRound
  | .keccak => .keccak

def HashSpan.controlRegister : HashSpan → BitVec 5
  | .blakeG _ | .blakeRound _ => 12
  | .keccak => 10

def HashSpan.controlStart : HashSpan → BitVec 32
  | .blakeG reduced => if reduced then 128 else 0
  | .blakeRound flags => BitVec.ofNat 32 ((8 + flags.val) * 65536)
  | .keccak => 0

def HashSpan.callCount : HashSpan → Nat
  | .blakeG reduced => Blake2G.callCount reduced
  | .blakeRound flags => if flags.val % 2 = 1 then 7 else 10
  | .keccak => 649

/-- Public mode/control and the existing homogeneous complete-span ABI.
    Span size is explicit; zero-clock worker exclusion and arbitrary ISA
    interleaving are separate. No intermediate state or output is supplied. -/
structure HashSpan.Protocol [Fact p.Prime] (workers : MemoryData p)
    (before : State) (span : HashSpan) : Prop where
  /-- The same modeled tables used by the existing complete-span proofs. -/
  tables : workers.setup = modeledSetup Keccak.Controller.rows
  /-- Every native worker belongs to this single uninterrupted protocol. -/
  family : ∀ row ∈ workers.rows, row.family = span.family
  /-- Actual initial architectural control read, with the public mode/flags. -/
  controlStart : (Cell.register span.controlRegister).read before = .ok span.controlStart before
  /-- Existing caller ABI span size, not a derived fulfillment-exclusion claim. -/
  calls : workers.rows.length = span.callCount

/-- One complete worker span in the caller-only shared architecture.
    Both public initialization and the existing protocol ABI stay visible. -/
structure SharedSpanInputs [Fact p.Prime] (data : RequestTrace p)
    (before : State) (addresses : List (BitVec 32)) (cells : List Cell)
    (span : HashSpan) : Prop extends SharedMemoryInputs data before addresses cells,
      HashSpan.Protocol data.workers before span

/-- Every shared terminal token is read from the same actual final Sail state,
    including x0 caller tokens and all worker registers/RAM. -/
def SharedTerminalState [Fact p.Prime] (data : RequestTrace p) (after : State)
    (cells : List Cell) : Prop :=
  ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
    cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

/-- The already reviewed complete hash reference on actual initial/final RAM.
    `TraceMapping` connects the supplied native worker boundaries to that same
    final state. Caller claims derive those boundaries from shared matching. -/
def HashSpan.Result [Fact p.Prime] (span : HashSpan) (workers : MemoryData p)
    (before after : State) (cells : List Cell) : Prop :=
  match span with
  | .blakeG reduced =>
    ∃ statePointer messagePointer : BitVec 32, ∃ input message output : Vector Arithmetic.Word 16,
      Blake2G.WorkVector.WordMapping before after statePointer messagePointer input message output ∧
      Delegation.TraceMapping workers before after cells ∧
      output.map Arithmetic.Word.value = Blake2G.WorkVector.run reduced input message
  | .blakeRound flags =>
    ∃ statePointer messagePointer : BitVec 32, ∃ input : Blake2Round.Compression.State,
      ∃ message : Vector Arithmetic.Word 16, ∃ output : Blake2Round.Compression.State,
      Blake2Round.Compression.WordMapping before after statePointer messagePointer input output message ∧
      Delegation.TraceMapping workers before after cells ∧
      output = Blake2Round.Compression.run flags input message
  | .keccak =>
    ∃ pointer : BitVec 32, ∃ input output : Vector Nat 25,
      Keccak.Permutation.WordMapping before after pointer input output ∧
      Delegation.TraceMapping workers before after cells ∧
      output = Specs.Keccak256.keccakPermutation input

abbrev SpanResult [Fact p.Prime] (span : HashSpan) (data : RequestTrace p)
    (before after : State) (cells : List Cell) : Prop :=
  span.Result data.workerProjection before after (workerCells cells)

/-- Original decoded requests, the complete existing hash reference, and all
    shared terminal values are connected. Caller PC retirement and unrestricted
    mixed-ISA/span segmentation are outside this architectural-memory claim. -/
structure SharedSpanEffects [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (span : HashSpan) : Prop where
  requests : RequestBinding data before
  /-- Hash output and shared terminal tokens refer to this one actual final state. -/
  result : ∃ after, SharedTerminalState data after cells ∧ SpanResult span data before after cells

end Airbender.Delegation.Caller
