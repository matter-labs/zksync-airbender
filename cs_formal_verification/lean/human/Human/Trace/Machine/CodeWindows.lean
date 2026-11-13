module
public import Human.Trace.Machine.Segmentation

@[expose] public section
namespace Airbender.Trace.Machine
open Delegation

/-- Public code and duration for one complete hash interval. No worker count or result is supplied. -/
structure CodeWindowScope {Kind : Type} [CircuitLayout Kind]
    (trace : Data babyBearModulus Kind) (program : List RVMachineProgramEntry) (window : HashWindow) : Prop where
  /-- The interval starts after the public native initial clock. -/
  afterInitial : (timeOfPair trace.initial.timestamp).value ≤ window.lower
  /-- The interval ends inside the native state path. -/
  beforeTerminal : window.upper ≤ (timeOfPair trace.terminal.timestamp).value
  /-- The first cut is an instruction boundary. -/
  firstAligned : window.lower % 4 = 0
  /-- The last cut is an instruction boundary. -/
  lastAligned : window.upper % 4 = 0
  /-- The public duration is the complete independent protocol length. -/
  duration : window.upper = window.lower + 4 * window.protocol.kinds.length
  /-- Every fetched public entry in this interval is a CSR of this protocol. -/
  code : ∀ row ∈ trace.rows, window.lower ≤ row.clock ∧ row.clock < window.upper →
    ∀ entry ∈ program, row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)) →
      ∃ kind ∈ window.protocol.kinds, RV.decode entry.bits = some (.delegate kind)

/-- Unrolled hash segmentation derives every protocol count and CSR family from public decoded code and duration. -/
def UnrolledCodeHashSegmentationClaim : Prop :=
  ∀ config (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) addresses program windows,
    config ≠ .unified → rvMachineProgramImage config initial addresses = some program →
    UnrolledAcceptance trace workers program →
    (timeOfPair trace.initial.timestamp).Bounded → (timeOfPair trace.initial.timestamp).value % 4 = 0 →
    windows.Pairwise (fun first second => first.upper ≤ second.lower) →
    (∀ request ∈ (unrolledCallers trace).map (fun row => Requests.caller row.assignment),
      request.csr ≠ Requests.csr .bigint ↔ ∃ window ∈ windows, window.select request = true) →
    (∀ window ∈ windows, CodeWindowScope trace program window) → IssuedHashSegmentation workers.fulfillments windows

/-- Unified hash segmentation derives every protocol count and CSR family from the same public code interface. -/
def UnifiedCodeHashSegmentationClaim : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) addresses program windows,
    rvMachineProgramImage .unified initial addresses = some program → UnifiedAcceptance trace workers program →
    (timeOfPair trace.initial.timestamp).Bounded → (timeOfPair trace.initial.timestamp).value % 4 = 0 →
    windows.Pairwise (fun first second => first.upper ≤ second.lower) →
    (∀ request ∈ (trace.rows.filter (fun row => decide (UnifiedReduced.Caller.Selected row.assignment))).map
      (fun row => UnifiedReduced.Caller.request row.assignment),
      request.csr ≠ Requests.csr .bigint ↔ ∃ window ∈ windows, window.select request = true) →
    (∀ window ∈ windows, CodeWindowScope trace program window) → IssuedHashSegmentation workers.fulfillments windows

end Airbender.Trace.Machine
