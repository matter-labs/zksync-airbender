module
public import Proven.Compiler.WorkerWitnesses.Standard
public import Proven.Compiler.WorkerWitnesses.Split
public import Proven.Compiler.WorkerConstraints

@[expose] public section
namespace Airbender.Compiler
open NativeArithmetic
set_option warningAsError true

/-- Every production worker used by the targets has a full active cached certificate with public lookups. -/
theorem cached_worker_certificates_satisfiable (family : NativeWorkerLookups.Family) :
    ∃ entry : WorkerCertificate, entry.family = family := by
  cases family with
  | bigint => exact ⟨WorkerWitnesses.bigint, rfl⟩
  | blakeG => exact ⟨WorkerWitnesses.blakeG, rfl⟩
  | blakeRound => exact ⟨WorkerWitnesses.blakeRound, rfl⟩
  | columnParity => exact ⟨WorkerWitnesses.columnParity, rfl⟩
  | thetaRho => exact ⟨WorkerWitnesses.thetaRho, rfl⟩
  | chi5 => exact ⟨WorkerWitnesses.chi5, rfl⟩

/-- A cached standard worker certificate implies its full row constraints and participation flag. -/
theorem native_standard_worker_row (entry : WorkerCertificate)
    (row : Delegation.Row babyBearModulus) (represented : entry.standardRow = some row) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints (Delegation.modeledSetup Keccak.Controller.rows)) ∧
      row.assignment row.columns.execute = 1 :=
  WorkerConstraints.standard_facts entry row represented

/-- A cached split worker certificate implies its full row constraints and participation flag. -/
theorem native_split_worker_row (entry : WorkerCertificate)
    (row : Keccak.Split.Native.Row babyBearModulus) (represented : entry.splitRow = some row) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints ∧
      row.assignment row.columns.execute = 1 :=
  WorkerConstraints.split_facts entry row represented

end Airbender.Compiler
