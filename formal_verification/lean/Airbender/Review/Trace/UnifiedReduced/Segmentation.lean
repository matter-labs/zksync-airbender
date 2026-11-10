import Airbender.Review.Trace.UnifiedReduced.ComputedRoundRegions

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Every occurrence of public hash CSR code belongs to a selected complete
    protocol window of the same family. Bigint callers may remain in gaps.
    Quantification over native clocks retains repeated RV32 code addresses. -/
def ProgramHashCallerCoverage [Fact p.Prime] (data : RequestTrace p)
    (windows : List HashWindow) : Prop :=
  ∀ entry ∈ data.program, entry.data.family ≠ .bigint →
    ∀ clock, (timeOfPair data.machine.initial.timestamp).value ≤ clock →
      clock + 4 ≤ (timeOfPair data.machine.terminal.timestamp).value → clock % 4 = 0 →
      entry.pc = wrappedProgramAddress data clock →
      ∃ window ∈ windows, window.lower ≤ clock ∧ clock < window.upper ∧
        window.span.family = entry.data.family

/-- The exact participating hash workers with actual matched nonzero requests.
    Zero-clock workers remain outside this list with their architectural effects. -/
def issuedHashWorkers [Fact p.Prime] (data : RequestTrace p) : List (Delegation.Row p) :=
  data.workers.rows.filter fun worker => decide
    (worker.family ≠ .bigint ∧ Delegation.Requests.Live (Delegation.Requests.fulfillment worker))

/-- Complete-window membership partitions all issued hash requests, including
    multiplicity. Coverage and unique assignment are conclusions of public code
    coverage, native matching and ordered cuts. This is not full CSR retirement. -/
structure IssuedHashSegmentation [Fact p.Prime] (data : RequestTrace p)
    (windows : List HashWindow) : Prop where
  workers : (windows.flatMap fun window => data.workers.windowRows window.lower window.upper).Perm
    (issuedHashWorkers data)
  unique : ∀ worker ∈ data.workers.rows, worker.family ≠ .bigint →
    Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
    ∃! window, window ∈ windows ∧ worker ∈ data.workers.windowRows window.lower window.upper
  requests : (windows.flatMap fun window =>
      (Delegation.Caller.windowCallers data.callers window.lower window.upper).map
        (fun caller => Delegation.Requests.caller caller.assignment)).Perm
    ((issuedHashWorkers data).map Delegation.Requests.fulfillment)
  calls : (windows.map fun window => window.span.callCount).sum = (issuedHashWorkers data).length
  residual : ∀ worker ∈ data.workers.rows, worker.family ≠ .bigint →
    ((∀ window ∈ windows, worker ∉ data.workers.windowRows window.lower window.upper) ↔
      (Delegation.Requests.fulfillment worker).time = (0, 0))

/-- The existing complete references in one initialized history, together with
    total issued-hash coverage. Ordinary/bigint gaps and the zero-clock prefix
    retain their actual effects. Public protocol and modeled-table scope remain. -/
def SegmentedHashSequenceResult [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (first : HashWindow) (rest : List HashWindow) : Prop :=
  IssuedHashSegmentation data (first :: rest) ∧ PreparedHashSequenceResult data before cells first rest

end Airbender.UnifiedReduced.Caller
