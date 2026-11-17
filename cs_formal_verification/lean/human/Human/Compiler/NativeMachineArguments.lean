module
public import Human.Compiler.LookupSelectors
public import Human.Compiler.WorkerCertificates
public import Human.Trace.Machine.Model
public import Human.Trace.Machine.Padding

@[expose] public section
namespace Airbender.Compiler
open Airbender.Trace
open NativeArithmetic

/-- Each setup index belongs to the current captured native trace domain. -/
abbrev NativeSetupIndex (family : RVMachineDecoderFamily) :=
  Fin (NativeLookups.circuitFor family).trace_len

/-- Public setup rows have the current circuit domain and native lookup-group order. -/
abbrev ProgramLookupRows := (family : RVMachineDecoderFamily) → Fin 3 → NativeSetupIndex family → List F

/-- A cached CPU row supplies actual physical equations and exact uncompressed lookup matching.
    Placement binds the logical witness to the current capture.
    No imported constraint or decoder-membership conclusion is a certificate field. -/
structure ProgramRowCertificate (tables : ProgramLookupRows) where
  /-- The CPU family and its logical witness assignment. -/
  row : Trace.Row babyBearModulus PooledFamily
  /-- Values at the native physical addresses. -/
  physical : GKRAddress → F
  /-- All native base-field gates and scalar caches hold. -/
  arithmetic : Holds (NativeLookups.circuitFor (.pooled row.family)) physical
  /-- Every captured source placement reads the same logical witness value. -/
  placement : PlacementAgreement (NativeLookups.circuitFor (.pooled row.family)) physical row.assignment
  /-- Enabled native tuples match independently interpreted public setup rows with natural counts. -/
  lookups : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled row.family))
    (NativeLookups.selectorsFor (.pooled row.family)) physical (tables (.pooled row.family))

/-- A participating cached CPU row. Participation binds the execute column. -/
structure ProgramLogicalRowCertificate (tables : ProgramLookupRows) extends ProgramRowCertificate tables where
  /-- The CPU row participates in the native argument. -/
  active : row.assignment row.columns.execute = 1

/-- The unified cached row uses the same physical and logical boundary. -/
structure UnifiedRowCertificate (tables : ProgramLookupRows) where
  /-- The unified CPU witness assignment. -/
  row : Trace.Row babyBearModulus UnifiedFamily
  /-- Values at the native physical addresses. -/
  physical : GKRAddress → F
  /-- All native base-field gates and scalar caches hold. -/
  arithmetic : Holds (NativeLookups.circuitFor .unified) physical
  /-- Every captured source placement reads the same logical witness value. -/
  placement : PlacementAgreement (NativeLookups.circuitFor .unified) physical row.assignment
  /-- Enabled native tuples match independently interpreted public setup rows with natural counts. -/
  lookups : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
    (NativeLookups.selectorsFor .unified) physical (tables .unified)

/-- A participating unified cached row. -/
structure UnifiedLogicalRowCertificate (tables : ProgramLookupRows) extends UnifiedRowCertificate tables where
  /-- The unified CPU row participates in the native argument. -/
  active : row.assignment row.columns.execute = 1

/-- Cached CPU and worker certificates supply native equations, source placement and exact public lookups.
    Raw state matching, request matching and architectural memory matching are explicit interfaces. -/
structure UnrolledNativeArguments (tables : ProgramLookupRows)
    (certificates : List (ProgramLogicalRowCertificate tables))
    (trace : PooledTrace babyBearModulus) (workers : Machine.WorkerPools babyBearModulus) : Prop
    where
  /-- Native worker certificates describe both submitted worker pools exactly, in order. -/
  workerRows : WorkerRowsCertified workers
  /-- Certificates describe exactly the submitted CPU rows, in order. -/
  rows : trace.rows = certificates.map (·.row)
  /-- The initial, row and terminal raw state tuples balance. -/
  states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start)
  /-- Every selected caller matches the complete submitted worker multiset. -/
  requests : Delegation.Requests.Matching
    ((Machine.unrolledCallers trace).map fun row => Delegation.Requests.caller row.assignment)
    workers.fulfillments
  /-- CPU and worker memory transfers share the initialized native memory permutation. -/
  memory : (trace.initialMemory ++ (Machine.unrolledSteps trace ++ workers.steps).map Prod.snd).Perm
    (trace.terminalMemory ++ (Machine.unrolledSteps trace ++ workers.steps).map Prod.fst)

/-- The unified cached interface retains the same independent matching boundaries. -/
structure UnifiedNativeArguments (tables : ProgramLookupRows)
    (certificates : List (UnifiedLogicalRowCertificate tables))
    (trace : UnifiedTrace babyBearModulus) (workers : Machine.WorkerPools babyBearModulus) : Prop
    where
  /-- Native worker certificates describe both submitted worker pools exactly, in order. -/
  workerRows : WorkerRowsCertified workers
  /-- Certificates describe exactly the submitted CPU rows, in order. -/
  rows : trace.rows = certificates.map (·.row)
  /-- The initial, row and terminal raw state tuples balance. -/
  states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start)
  /-- Every selected unified caller matches the complete submitted worker multiset. -/
  requests : Delegation.Requests.Matching
    ((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) workers.fulfillments
  /-- CPU and worker memory transfers share the initialized native memory permutation. -/
  memory : (trace.initialMemory ++ (Machine.unifiedSteps trace ++ workers.steps).map Prod.snd).Perm
    (trace.terminalMemory ++ (Machine.unifiedSteps trace ++ workers.steps).map Prod.fst)

/-- The padded unrolled layout: cached CPU and worker certificates for active and padding rows.
    The state, request and memory relations keep every row occurrence under the native execute mask. -/
structure PaddedUnrolledNativeArguments (tables : ProgramLookupRows)
    (certificates : List (ProgramRowCertificate tables))
    (trace : PooledTrace babyBearModulus) (workers : Machine.WorkerPools babyBearModulus) : Prop
    where
  /-- Native worker certificates describe both submitted worker pools exactly, in order. -/
  workerRows : PaddedWorkerRowsCertified workers
  /-- Certificates describe exactly the submitted CPU rows, in order. -/
  rows : trace.rows = certificates.map (·.row)
  /-- Each CPU execute selector is Boolean: one marks an active row and zero a padding row. -/
  selectors : ∀ certificate ∈ certificates,
    certificate.row.assignment certificate.row.columns.execute = 0 ∨
      certificate.row.assignment certificate.row.columns.execute = 1
  /-- The masked initial, row and terminal raw state tuples balance. -/
  states : (some trace.initial :: PaddingBoundary.contributions trace.rows
    (fun row => row.assignment row.columns.execute) (fun row => [row.finish])).Perm
      (some trace.terminal :: PaddingBoundary.contributions trace.rows
        (fun row => row.assignment row.columns.execute) (fun row => [row.start]))
  /-- The masked callers match the complete masked worker multiset. -/
  requests : (Machine.maskedUnrolledRequests trace Delegation.Requests.Request.issued ++
      Machine.maskedWorkerRequests workers Delegation.Requests.Request.empty).Perm
    (Machine.maskedUnrolledRequests trace Delegation.Requests.Request.empty ++
      Machine.maskedWorkerRequests workers Delegation.Requests.Request.issued)
  /-- Masked CPU and worker memory transfers share the initialized native memory permutation. -/
  memory : (trace.initialMemory.map some ++ Machine.maskedUnrolledTokens trace Prod.snd ++
      Machine.maskedWorkerTokens workers Prod.snd).Perm
    (trace.terminalMemory.map some ++ Machine.maskedUnrolledTokens trace Prod.fst ++
      Machine.maskedWorkerTokens workers Prod.fst)

/-- The padded unified layout keeps the same masked native boundary. -/
structure PaddedUnifiedNativeArguments (tables : ProgramLookupRows)
    (certificates : List (UnifiedRowCertificate tables))
    (trace : UnifiedTrace babyBearModulus) (workers : Machine.WorkerPools babyBearModulus) : Prop
    where
  /-- Native worker certificates describe both submitted worker pools exactly, in order. -/
  workerRows : PaddedWorkerRowsCertified workers
  /-- Certificates describe exactly the submitted CPU rows, in order. -/
  rows : trace.rows = certificates.map (·.row)
  /-- Each CPU execute selector is Boolean: one marks an active row and zero a padding row. -/
  selectors : ∀ certificate ∈ certificates,
    certificate.row.assignment certificate.row.columns.execute = 0 ∨
      certificate.row.assignment certificate.row.columns.execute = 1
  /-- The masked initial, row and terminal raw state tuples balance. -/
  states : (some trace.initial :: PaddingBoundary.contributions trace.rows
    (fun row => row.assignment row.columns.execute) (fun row => [row.finish])).Perm
      (some trace.terminal :: PaddingBoundary.contributions trace.rows
        (fun row => row.assignment row.columns.execute) (fun row => [row.start]))
  /-- The masked unified callers match the complete masked worker multiset. -/
  requests : (Machine.maskedUnifiedRequests trace Delegation.Requests.Request.issued ++
      Machine.maskedWorkerRequests workers Delegation.Requests.Request.empty).Perm
    (Machine.maskedUnifiedRequests trace Delegation.Requests.Request.empty ++
      Machine.maskedWorkerRequests workers Delegation.Requests.Request.issued)
  /-- Masked CPU and worker memory transfers share the initialized native memory permutation. -/
  memory : (trace.initialMemory.map some ++ Machine.maskedUnifiedTokens trace Prod.snd ++
      Machine.maskedWorkerTokens workers Prod.snd).Perm
    (trace.terminalMemory.map some ++ Machine.maskedUnifiedTokens trace Prod.fst ++
      Machine.maskedWorkerTokens workers Prod.fst)

end Airbender.Compiler
