import Airbender.Review.Helpers.Delegation.WorkerProjection
import Airbender.Review.Circuits.Blake2G.Protocol
import Airbender.Review.Helpers.Delegation.Operations
import Airbender.Review.Circuits.Keccak.Tables.Controller

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

end Airbender.Delegation.Caller
