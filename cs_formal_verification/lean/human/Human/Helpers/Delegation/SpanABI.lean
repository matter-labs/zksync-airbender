import Human.Helpers.Delegation.WorkerProjection
import Human.Circuits.Blake2G.Protocol
import Human.Helpers.Delegation.Operations
import Human.Circuits.Keccak.Tables.Controller

namespace Airbender.Delegation.Caller
open Trace

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

end Airbender.Delegation.Caller
