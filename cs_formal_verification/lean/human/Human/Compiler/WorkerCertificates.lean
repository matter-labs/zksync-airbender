module
public import Human.Compiler.WorkerPublicSetup
public import Human.Trace.Machine.Model

@[expose] public section
namespace Airbender.Compiler
open NativeArithmetic NativeWorkerLookups

/-- The execute column comes from the worker's imported delegation metadata. -/
noncomputable def workerColumns : NativeWorkerLookups.Family → Delegation.ClockColumns
  | .bigint => Bigint.importedConstraintsDelegationColumns
  | .blakeG => Blake2G.importedConstraintsDelegationColumns
  | .blakeRound => Blake2Round.importedConstraintsDelegationColumns
  | .columnParity => Keccak.Split.ColumnParity.importedConstraintsDelegationColumns
  | .thetaRho => Keccak.Split.ThetaRho.importedConstraintsDelegationColumns
  | .chi5 => Keccak.Split.Chi5.importedConstraintsDelegationColumns

/-- A worker row has native cached equations, source placement and exact public lookup matching. -/
structure WorkerCertificate where
  /-- The cached production worker. -/
  family : NativeWorkerLookups.Family
  /-- Values at the worker's logical source columns. -/
  assignment : Nat → F
  /-- Values at every native physical address. -/
  physical : GKRAddress → F
  /-- Every native base-field gate and scalar cache holds. -/
  arithmetic : Holds (NativeWorkerLookups.circuitFor family) physical
  /-- The imported source placements agree with the logical assignment. -/
  placement : PlacementAgreement (NativeWorkerLookups.circuitFor family) physical assignment
  /-- Every enabled native lookup tuple matches its public worker table with natural counts. -/
  lookups : NativeLookups.Arguments (NativeWorkerLookups.circuitFor family)
    (NativeWorkerLookups.selectorsFor family) physical (NativeWorkerSetup.rows family)
  /-- This row participates in the worker argument. -/
  active : assignment (workerColumns family).execute = 1

/-- A standard certificate describes a standard submitted worker row. -/
def WorkerCertificate.standardRow (certificate : WorkerCertificate) : Option (Delegation.Row babyBearModulus) :=
  match certificate.family with
  | .bigint => some ⟨.bigint, certificate.assignment⟩
  | .blakeG => some ⟨.blakeG, certificate.assignment⟩
  | .blakeRound => some ⟨.blakeRound, certificate.assignment⟩
  | _ => none

/-- A split certificate describes a split submitted worker row. -/
def WorkerCertificate.splitRow (certificate : WorkerCertificate) : Option (Keccak.Split.Native.Row babyBearModulus) :=
  match certificate.family with
  | .columnParity => some ⟨.columnParity, certificate.assignment⟩
  | .thetaRho => some ⟨.thetaRho, certificate.assignment⟩
  | .chi5 => some ⟨.chi5, certificate.assignment⟩
  | _ => none

/-- Native certificates describe exactly each submitted worker pool, in its submitted order. -/
def WorkerRowsCertified (workers : Trace.Machine.WorkerPools babyBearModulus) : Prop :=
  ∃ certificates : List WorkerCertificate,
    workers.standard.rows = certificates.filterMap WorkerCertificate.standardRow ∧
    workers.split.rows = certificates.filterMap WorkerCertificate.splitRow

end Airbender.Compiler
