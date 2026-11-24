module
public import Human.Compiler.NativeTargets
public import Proven.Trace.Machine.PaddingProjection

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Airbender.Compiler Delegation PaddingBoundary PaddingBoundary.Proofs
set_option warningAsError true

/-- The participating CPU certificates of a padded layout, in submitted order. -/
noncomputable def activeCertificates {tables : ProgramLookupRows} :
    List (ProgramRowCertificate tables) → List (ProgramLogicalRowCertificate tables)
  | [] => []
  | certificate :: rest =>
    if selected : certificate.row.assignment certificate.row.columns.execute = 1 then
      { toProgramRowCertificate := certificate, active := selected } :: activeCertificates rest
    else activeCertificates rest

theorem activeCertificates_rows {tables : ProgramLookupRows} (certificates : List (ProgramRowCertificate tables)) :
    (activeCertificates certificates).map (·.row) =
      (certificates.map (·.row)).filter fun row => decide (row.assignment row.columns.execute = 1) := by
  induction certificates with
  | nil => rfl
  | cons certificate rest proof =>
    unfold activeCertificates
    split <;> simp_all

/-- The participating unified certificates of a padded layout, in submitted order. -/
noncomputable def activeUnifiedCertificates {tables : ProgramLookupRows} :
    List (UnifiedRowCertificate tables) → List (UnifiedLogicalRowCertificate tables)
  | [] => []
  | certificate :: rest =>
    if selected : certificate.row.assignment certificate.row.columns.execute = 1 then
      { toUnifiedRowCertificate := certificate, active := selected } :: activeUnifiedCertificates rest
    else activeUnifiedCertificates rest

theorem activeUnifiedCertificates_rows {tables : ProgramLookupRows}
    (certificates : List (UnifiedRowCertificate tables)) :
    (activeUnifiedCertificates certificates).map (·.row) =
      (certificates.map (·.row)).filter fun row => decide (row.assignment row.columns.execute = 1) := by
  induction certificates with
  | nil => rfl
  | cons certificate rest proof =>
    unfold activeUnifiedCertificates
    split <;> simp_all

/-- The participating worker certificates of a padded layout, in submitted order. -/
noncomputable def activeWorkerCertificates : List WorkerRowCertificate → List WorkerCertificate
  | [] => []
  | certificate :: rest =>
    if selected : certificate.assignment (workerColumns certificate.family).execute = 1 then
      { toWorkerRowCertificate := certificate, active := selected } :: activeWorkerCertificates rest
    else activeWorkerCertificates rest

/-- A standard worker row reads the execute column of its certificate. -/
theorem standardRow_execute (certificate : WorkerRowCertificate) (row : Delegation.Row babyBearModulus)
    (represented : certificate.standardRow = some row) :
    row.assignment row.columns.execute = certificate.assignment (workerColumns certificate.family).execute := by
  rcases certificate with ⟨family, assignment, physical, arithmetic, placement, lookups⟩
  cases family <;> simp only [WorkerRowCertificate.standardRow, reduceCtorEq, Option.some.injEq] at represented <;>
    subst represented <;> rfl

/-- A split worker row reads the execute column of its certificate. -/
theorem splitRow_execute (certificate : WorkerRowCertificate) (row : Keccak.Split.Native.Row babyBearModulus)
    (represented : certificate.splitRow = some row) :
    row.assignment row.columns.execute = certificate.assignment (workerColumns certificate.family).execute := by
  rcases certificate with ⟨family, assignment, physical, arithmetic, placement, lookups⟩
  cases family <;> simp only [WorkerRowCertificate.splitRow, reduceCtorEq, Option.some.injEq] at represented <;>
    subst represented <;> rfl

theorem activeWorkerCertificates_standard (certificates : List WorkerRowCertificate) :
    (activeWorkerCertificates certificates).filterMap (·.standardRow) =
      (certificates.filterMap (·.standardRow)).filter fun row => decide (row.assignment row.columns.execute = 1) := by
  induction certificates with
  | nil => rfl
  | cons certificate rest proof =>
    unfold activeWorkerCertificates
    cases represented : certificate.standardRow with
    | none =>
      split <;> simp [represented, proof]
    | some row =>
      have same := standardRow_execute certificate row represented
      split
      · next selected => simp [represented, proof, same, selected]
      · next unselected => simp [represented, proof, same, unselected]

theorem activeWorkerCertificates_split (certificates : List WorkerRowCertificate) :
    (activeWorkerCertificates certificates).filterMap (·.splitRow) =
      (certificates.filterMap (·.splitRow)).filter fun row => decide (row.assignment row.columns.execute = 1) := by
  induction certificates with
  | nil => rfl
  | cons certificate rest proof =>
    unfold activeWorkerCertificates
    cases represented : certificate.splitRow with
    | none =>
      split <;> simp [represented, proof]
    | some row =>
      have same := splitRow_execute certificate row represented
      split
      · next selected => simp [represented, proof, same, selected]
      · next unselected => simp [represented, proof, same, unselected]

/-- Padded worker certificates describe exactly the active worker rows. -/
theorem padded_worker_rows {workers : WorkerPools babyBearModulus} (certified : PaddedWorkerRowsCertified workers) :
    WorkerRowsCertified (activeWorkers workers) := by
  obtain ⟨certificates, _, standard, split⟩ := certified
  refine ⟨activeWorkerCertificates certificates, ?_, ?_⟩
  · simp only [activeWorkers, standard]
    exact (activeWorkerCertificates_standard certificates).symm
  · simp only [activeWorkers, split]
    exact (activeWorkerCertificates_split certificates).symm

/-- A padded unrolled layout gives the native arguments of its active rows. -/
theorem padded_unrolled_arguments {tables : ProgramLookupRows} {certificates : List (ProgramRowCertificate tables)}
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    (arguments : PaddedUnrolledNativeArguments tables certificates trace workers) :
    UnrolledNativeArguments tables (activeCertificates certificates) (active trace) (activeWorkers workers) where
  workerRows := padded_worker_rows arguments.workerRows
  rows := by
    simp only [active, arguments.rows]
    exact (activeCertificates_rows certificates).symm
  states := by
    have matched := arguments.states.filterMap (fun value => value)
    simpa only [List.filterMap_cons, erase_contributions, flatMap_values, active] using matched
  requests := by
    have matched := arguments.requests.filterMap (fun value => value)
    simpa only [List.filterMap_append, erase_unrolled_requests, erase_worker_requests, Requests.Matching] using matched
  memory := by
    have matched := arguments.memory.filterMap (fun value => value)
    simpa only [List.filterMap_append, List.filterMap_map, Function.comp_def, List.filterMap_some,
      erase_unrolled_tokens, erase_worker_tokens, List.map_append, List.append_assoc, active] using matched

/-- A padded unified layout gives the native arguments of its active rows. -/
theorem padded_unified_arguments {tables : ProgramLookupRows} {certificates : List (UnifiedRowCertificate tables)}
    {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    (arguments : PaddedUnifiedNativeArguments tables certificates trace workers) :
    UnifiedNativeArguments tables (activeUnifiedCertificates certificates) (active trace) (activeWorkers workers) where
  workerRows := padded_worker_rows arguments.workerRows
  rows := by
    simp only [active, arguments.rows]
    exact (activeUnifiedCertificates_rows certificates).symm
  states := by
    have matched := arguments.states.filterMap (fun value => value)
    simpa only [List.filterMap_cons, erase_contributions, flatMap_values, active] using matched
  requests := by
    have matched := arguments.requests.filterMap (fun value => value)
    simpa only [List.filterMap_append, erase_unified_requests, erase_worker_requests, Requests.Matching] using matched
  memory := by
    have matched := arguments.memory.filterMap (fun value => value)
    simpa only [List.filterMap_append, List.filterMap_map, Function.comp_def, List.filterMap_some,
      erase_unified_tokens, erase_worker_tokens, List.map_append, List.append_assoc, active] using matched

end Airbender.Trace.Machine.Proofs
