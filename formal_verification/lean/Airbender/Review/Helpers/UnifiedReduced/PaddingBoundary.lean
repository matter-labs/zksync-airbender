import Airbender.Review.Helpers.Context.PaddingBoundary.Model
import Airbender.Review.Helpers.UnifiedReduced.MixedMemory

namespace Airbender.UnifiedReduced.Caller.Padding
open Trace PaddingBoundary

/-- Execute flags select machine and worker occurrences independently. Invocation
    clock zero is not padding: an execute-one zero-clock worker is retained. -/
def active [Fact p.Prime] (data : RequestTrace p) : RequestTrace p :=
  { data with
    machine := PaddingBoundary.active data.machine
    workers := { data.workers with rows := data.workers.rows.filter (fun row => decide (row.assignment row.columns.execute = 1)) } }

/-- Actual architectural machine ports, excluding the virtual caller CSR port. -/
def machineContributions [Fact p.Prime] (data : RequestTrace p) (write : Bool) :=
  contributions data.machine.rows (fun row => row.assignment row.columns.execute) fun row =>
    (machinePorts row).toList.map fun port =>
      if write then writeToken row.columns row.assignment port else readToken row.assignment port

/-- All four workers' actual fixed/indirect ports use their native execute flag. -/
def workerContributions [Fact p.Prime] (data : RequestTrace p) (write : Bool) :=
  contributions data.workers.rows (fun row => row.assignment row.columns.execute) fun row =>
    row.memorySteps.map fun edge => if write then edge.2 else edge.1

/-- Shared GPR/RAM contributions over the complete unfiltered layout. -/
def memoryContributions [Fact p.Prime] (data : RequestTrace p) (write : Bool) :=
  machineContributions data write ++ workerContributions data write

/-- Full-CSR virtual tokens for actual native caller candidates. Execute-zero
    candidates contribute identities even if their decoder caller flag is set. -/
def callerContributions [Fact p.Prime] (data : RequestTrace p) (issued : Bool) :=
  contributions data.callers (fun row => row.assignment row.columns.execute) fun row =>
    [if issued then (request row.assignment).issued else (request row.assignment).empty]

/-- All fulfillment occurrences, including execute-one zero-clock workers. -/
def fulfillmentContributions [Fact p.Prime] (data : RequestTrace p) (issued : Bool) :=
  contributions data.workers.rows (fun row => row.assignment row.columns.execute) fun row =>
    [if issued then (Delegation.Requests.fulfillment row).issued else (Delegation.Requests.fulfillment row).empty]

/-- External exact logical closure over the whole masked machine/worker layout.
    All masks are definitionally the native imported execute columns; full raw
    tuple values and identity factors are retained. Address-space projection,
    compiled selector copies, GKR/cryptographic enforcement and Rust/artifact
    correspondence remain external, as for the canonical verifier-PC boundary.
    No valid bigint control, positive invocation or worker output is assumed. -/
structure Binding [Fact p.Prime] (data : RequestTrace p) : Prop where
  machineSelectors : ∀ row ∈ data.machine.rows,
    row.assignment row.columns.execute = 0 ∨ row.assignment row.columns.execute = 1
  workerSelectors : ∀ row ∈ data.workers.rows,
    row.assignment row.columns.execute = 0 ∨ row.assignment row.columns.execute = 1
  /-- Machine PC/clock tuples and actual public endpoints. -/
  states : (some data.machine.initial :: contributions data.machine.rows
    (fun row => row.assignment row.columns.execute) (fun row => [row.finish])).Perm
      (some data.machine.terminal :: contributions data.machine.rows
        (fun row => row.assignment row.columns.execute) (fun row => [row.start]))
  /-- Unified architectural memory and every worker share one masked argument. -/
  memory : (data.machine.initialMemory.map some ++ memoryContributions data true).Perm
    (data.machine.terminalMemory.map some ++ memoryContributions data false)
  /-- Virtual CSR matching is kept separate from initialized GPR/RAM memory. -/
  requests : (callerContributions data true ++ fulfillmentContributions data false).Perm
    (callerContributions data false ++ fulfillmentContributions data true)

/-- Actual imported constraints/lookups hold on every raw row. Decoder membership
    applies only to selected occurrences, matching the masked decoder query.
    Ungated auxiliary lookups are never discarded by this contract. -/
structure AcceptedLayout [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) : Prop where
  constraints : ∀ row ∈ data.machine.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.machine.rom)
  workerConstraints : ∀ row ∈ data.workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.workers.setup)
  /-- Existing full-width caller decoder schema, after execute selection. -/
  decoded : ∀ row ∈ (active data).callers,
    (decoderTable data.program).Contains #[] (decoderQuery row.assignment)
  /-- Existing standard/TRIADD/XORROT schema for the selected noncallers. -/
  ordinaryDecoded : ∀ row ∈ (active data).machine.rows, row ∉ (active data).callers →
    (UnifiedReduced.decoderTable program).Contains #[] row.decoderQuery
  binding : Binding data

end Airbender.UnifiedReduced.Caller.Padding
