import Airbender.Review.Compiler.MachineTargets
import Airbender.Review.Compiler.NativeSubwordSetup

namespace Airbender.Compiler.MachineTargets
open Airbender.Trace Airbender.Trace.NativeDecoder NativeProgramSetup
variable [Fact babyBearModulus.Prime]

/-- Native CPU certificates replace the CPU-equation and execute premises.
Worker equations and exact state, request and RAM matching remain explicit. -/
structure UnrolledNativeArguments (initial : Reference.RiscV.Sail.State)
    (columns : PooledFamily → List (List Source.BaseField))
    (certificates : List (PooledExecution.ProgramLogicalRowCertificate
      (unrolledProgramLookupRows initial columns)))
    (trace : PooledTrace babyBearModulus) (workers : Delegation.MemoryData babyBearModulus)
    (extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus))
    (extraRequests : List (Delegation.Requests.Request babyBearModulus)) : Prop where
  rows : trace.rows = certificates.map PooledExecution.ProgramLogicalRowCertificate.row
  workerEquations : ∀ row ∈ workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints workers.setup)
  workerActive : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1
  states : (trace.initial :: trace.rows.map Row.finish).Perm
    (trace.terminal :: trace.rows.map Row.start)
  requests : Delegation.Requests.Matching (pooledCalls trace)
    (workers.rows.map Delegation.Requests.fulfillment ++ extraRequests)
  ram : (trace.initialMemory ++
      (pooledSteps trace ++ workers.steps ++ extraSteps).map Prod.snd).Perm
    (trace.terminalMemory ++
      (pooledSteps trace ++ workers.steps ++ extraSteps).map Prod.fst)

/-- The unified native interface keeps the same three exact matching boundaries. -/
structure UnifiedNativeArguments (initial : Reference.RiscV.Sail.State)
    (columns : List (List Source.BaseField))
    (certificates : List (UnifiedExecution.ProgramLogicalRowCertificate
      (unifiedLookupRows initial columns)))
    (trace : UnifiedTrace babyBearModulus) (workers : Delegation.MemoryData babyBearModulus) : Prop where
  rows : trace.rows = certificates.map UnifiedExecution.ProgramLogicalRowCertificate.row
  workerEquations : ∀ row ∈ workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints workers.setup)
  workerActive : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1
  states : (trace.initial :: trace.rows.map Row.finish).Perm
    (trace.terminal :: trace.rows.map Row.start)
  requests : Delegation.Requests.Matching (unifiedCalls trace)
    (workers.rows.map Delegation.Requests.fulfillment)
  ram : (trace.initialMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.snd).Perm
    (trace.terminalMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.fst)

end Airbender.Compiler.MachineTargets
