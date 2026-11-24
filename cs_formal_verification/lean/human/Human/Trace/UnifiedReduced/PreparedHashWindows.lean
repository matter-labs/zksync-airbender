module
public import Human.Helpers.UnifiedReduced.ControlPreparation
public import Human.Trace.UnifiedReduced.MixedWindows
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Human.Trace.Workers.Keccak.Permutation

@[expose] public section

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Public instruction literals for the existing hash protocol entry controls. -/
def hashPreparation : Delegation.Caller.HashSpan → ControlLiteral
  | .blakeG reduced => .addi (if reduced then 128 else 0)
  | .blakeRound flags => .lui (BitVec.ofNat 20 ((8 + flags.val) * 16))
  | .keccak => .addi 0

/-- A selected complete hash protocol and its public instruction-boundary cuts. -/
structure HashWindow where
  span : Delegation.Caller.HashSpan
  lower : Nat
  upper : Nat

/-- Native-memory interval used by the continuous sequence mapping. -/
def HashWindow.interval (window : HashWindow) : Nat × Nat := (window.lower, window.upper)

end Airbender.UnifiedReduced.Caller
