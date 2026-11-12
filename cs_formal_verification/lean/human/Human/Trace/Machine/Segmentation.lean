module
public import Human.Trace.Machine.Model
public import Human.ISA.DelegationRuns

@[expose] public section
namespace Airbender.Trace.Machine
open Delegation

/-- A complete production hash protocol. Bigint calls can occur between these windows. -/
inductive HashProtocol where
  | g (reduced : Bool)
  | round (reduced : Bool)
  | splitKeccak
  deriving DecidableEq

/-- The full independent CSR schedule of one complete protocol. -/
def HashProtocol.kinds : HashProtocol → List RV.DelegationKind
  | .g reduced => .replicate (if reduced then 56 else 80) .blakeG
  | .round reduced => .replicate (if reduced then 7 else 10) .blakeRound
  | .splitKeccak => RV.f1600Calls

/-- A public protocol interval uses instruction-boundary clocks. -/
structure HashWindow where
  /-- The complete protocol selected in this interval. -/
  protocol : HashProtocol
  /-- The first instruction-boundary clock. -/
  lower : Nat
  /-- The final instruction-boundary clock. -/
  upper : Nat

/-- The native caller and worker share this architectural retirement tick. -/
def requestTick (request : Requests.Request p) := (timeOfPair request.time).value + 3

/-- A worker request belongs to a half-open CPU window through its retirement tick. -/
def HashWindow.select (window : HashWindow) (request : Requests.Request p) : Bool :=
  decide (window.lower < requestTick request ∧ requestTick request ≤ window.upper)

/-- Retain the native request occurrences of a window. -/
def windowRequests (requests : List (Requests.Request p)) (window : HashWindow) := requests.filter window.select

/-- Hash requests exclude the single-call bigint operations in the intervening gaps. -/
def hashRequests (requests : List (Requests.Request p)) := requests.filter fun request => decide (request.csr ≠ Requests.csr .bigint)

/-- The public protocol-window interface uses caller occurrences, never worker outputs or a final execution. -/
structure HashWindowProfile (calls : List (Requests.Request p)) (windows : List HashWindow) : Prop where
  /-- Intervals are ordered and do not overlap. -/
  separated : windows.Pairwise (fun first second => first.upper ≤ second.lower)
  /-- Every hash caller occurrence belongs to a window; bigint gaps remain outside. -/
  coverage : ∀ request ∈ calls, request.csr ≠ Requests.csr .bigint ↔ ∃ window ∈ windows, window.select request = true
  /-- Each window has the independent protocol's number of caller occurrences. -/
  counts : ∀ window ∈ windows, (windowRequests calls window).length = window.protocol.kinds.length
  /-- Every selected full CSR belongs to that window's public protocol. -/
  families : ∀ window ∈ windows, ∀ request ∈ windowRequests calls window,
    request.csr ∈ window.protocol.kinds.map (fun kind => kind.csr.toNat)

/-- Complete hash windows partition all submitted hash worker requests with exact multiplicity. -/
structure IssuedHashSegmentation (fulfilled : List (Requests.Request p)) (windows : List HashWindow) : Prop where
  /-- The windows retain every submitted hash request occurrence. -/
  partition : (windows.flatMap (windowRequests fulfilled)).Perm (hashRequests fulfilled)
  /-- Each submitted hash request belongs to one interval. -/
  unique : ∀ request ∈ hashRequests fulfilled, ∃! window, window ∈ windows ∧ window.select request = true
  /-- The total protocol call count is the number of submitted hash requests. -/
  calls : (windows.map fun window => window.protocol.kinds.length).sum = (hashRequests fulfilled).length
  /-- Native full-CSR identities agree with each window's public protocol. -/
  families : ∀ window ∈ windows, ∀ request ∈ windowRequests fulfilled window,
    request.csr ∈ window.protocol.kinds.map (fun kind => kind.csr.toNat)
  /-- Active native hash workers cannot remain as zero-clock residuals. -/
  live : ∀ request ∈ hashRequests fulfilled, Requests.Live request

/-- Unrolled native request matching gives complete hash segmentation, including split Keccak. -/
def UnrolledHashSegmentationClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus) program windows,
    UnrolledAcceptance trace workers program →
    (timeOfPair trace.initial.timestamp).Bounded → (timeOfPair trace.initial.timestamp).value % 4 = 0 →
    HashWindowProfile ((unrolledCallers trace).map fun row => Requests.caller row.assignment) windows →
    IssuedHashSegmentation workers.fulfillments windows

/-- Unified native request matching gives the same occurrence-based hash segmentation. -/
def UnifiedHashSegmentationClaim : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus) program windows,
    UnifiedAcceptance trace workers program →
    (timeOfPair trace.initial.timestamp).Bounded → (timeOfPair trace.initial.timestamp).value % 4 = 0 →
    HashWindowProfile ((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) windows → IssuedHashSegmentation workers.fulfillments windows

end Airbender.Trace.Machine
