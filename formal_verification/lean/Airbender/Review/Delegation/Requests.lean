import Airbender.Review.Delegation.Memory
import Airbender.Review.AddSub.Artifact

namespace Airbender.Delegation.Requests
open Trace

/-- A delegation request's virtual CSR address and raw invocation clock.
    This is a permutation token, not an initialized architectural register.
    The CSR address is retained in full; it is never truncated to five bits. -/
structure Request (p : Nat) where
  csr : Nat
  time : ZMod p × ZMod p
  deriving DecidableEq

/-- Native zero-valued virtual-register token. The caller writes the invocation
    clock; fulfillment reads it and returns the zero-clock token.
    Source: `cs/src/gkr_compiler/memory_like_grand_product.rs`. -/
def Request.token (request : Request p) (time : ZMod p × ZMod p) : MemoryToken p :=
  ⟨Nat.pair 0 (Nat.pair request.csr 0), time, 0⟩

def Request.issued (request : Request p) := request.token request.time

def Request.empty (request : Request p) := request.token (0, 0)

/-- CSR identifiers from the pinned project's delegation constants:
    bigint=0x7CA, G=0x7C8, extended round=0x7C7, Keccak=0x7CB. -/
def csr : Family → Nat
  | .bigint => 0x7CA
  | .blakeG => 0x7C8
  | .blakeRound => 0x7C7
  | .keccak => 0x7CB

/-- Caller token from the actual ADD/SUB rs2 port and starting clock.
    This virtual port uses the imported in-cycle offset one. -/
def callerPort : MemoryPort := AddSub.importedConstraintsMemoryPorts[1]

/-- Native selector seven identifies a delegation caller. The descriptor
    comes from the same imported decoder placement used by other instructions. -/
def Selected (w : Nat → ZMod p) : Prop :=
  w AddSub.importedConstraintsDecoderColumns.flags[7] = 1

instance (w : Nat → ZMod p) : Decidable (Selected w) := inferInstanceAs
  (Decidable (w AddSub.importedConstraintsDecoderColumns.flags[7] = 1))

def caller (w : Nat → ZMod p) : Request p :=
  let initial := rawPair w AddSub.importedConstraintsTraceColumns.initialTime
  ⟨(w AddSub.importedConstraintsDecoderColumns.rs2).val,
    (initial.1 + callerPort.clock.offset, initial.2)⟩

/-- Fulfillment token from a family's native invocation columns. Activity
    selects participating rows separately; no caller is invented here. -/
def fulfillment (row : Row p) : Request p :=
  ⟨csr row.family, rawPair row.assignment row.columns.invocation⟩

/-- Exact logical matching of the virtual-register read/write contributions.
    Virtual addresses have no seed or terminal tokens. This is the explicit
    permutation boundary, separate from initialized GPR/RAM matching. -/
def Matching (calls fulfillments : List (Request p)) : Prop :=
  (calls.map Request.issued ++ fulfillments.map Request.empty).Perm
    (calls.map Request.empty ++ fulfillments.map Request.issued)

/-- Distinguish actual invocations from the returned zero-clock token.
    The caller's initialized machine clock proves this internally. Whether
    every active fulfillment enforces it remains a separate native obligation. -/
def Live (request : Request p) : Prop := request.time ≠ (0, 0)

instance (request : Request p) : Decidable (Live request) := inferInstanceAs
  (Decidable (request.time ≠ (0, 0)))

end Airbender.Delegation.Requests
