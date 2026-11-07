import Human.Trace.Delegation.RVCallerTheorems
import Slop.Delegation.RVSchedule
import Slop.Delegation.RVSharedOperations
import Slop.Delegation.RVSharedSpans
import Slop.Delegation.RVMixedMemory
import Slop.Delegation.RVRequestHashWindows

namespace Airbender.Delegation.Caller

/-- RV sibling of `requests_soundness`. -/
theorem rv_requests_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} (accepted : RVRequestAccepted data)
    (inputs : RVRequestInputs data before addresses) : RVRequestBinding data before :=
  Proofs.rv_request_binding hp clockInverse pcInverse accepted inputs

/-- RV sibling of `request_memory_soundness`. -/
theorem rv_request_memory_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : RVRequestAccepted data) (inputs : RVRequestMemoryInputs data before addresses cells) :
    RVRequestExecution data before cells :=
  Proofs.rv_request_memory_execution hp clockInverse pcInverse accepted inputs

/-- RV sibling of `operation_soundness`. -/
theorem rv_operation_soundness
    {data : RVRequestTrace babyBearModulus}
    {before : RV.State} {addresses : List (BitVec 32)}
    {cells : List Trace.Cell} (accepted : RVRequestAccepted data)
    (inputs : RVRequestOperationInputs data before addresses cells) :
    RVRequestOperationEffects data before cells :=
  Proofs.rv_request_operation_effects accepted inputs

/-- RV sibling of `shared_memory_soundness`. -/
theorem rv_shared_memory_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedMemoryInputs data before addresses cells) :
    RVSharedMemoryEffects data before cells :=
  Proofs.rv_shared_memory_execution hp clockInverse pcInverse accepted inputs

/-- RV sibling of `shared_operation_soundness`. -/
theorem rv_shared_operation_soundness
    {data : RVRequestTrace babyBearModulus} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedOperationInputs data before addresses cells) :
    RVSharedOperationEffects data before cells :=
  Proofs.rv_shared_operation_effects accepted inputs

/-- RV sibling of `shared_span_soundness`, with the delegate link in `HashSpan.RVResult`. -/
theorem rv_shared_span_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : HashSpan}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedSpanInputs data before addresses cells span) :
    RVSharedSpanEffects data before cells span :=
  Proofs.rv_shared_span_effects hp inverse accepted inputs

/-- RV sibling of `mixed_memory_soundness`. -/
theorem rv_mixed_memory_soundness
    {data : RVRequestTrace babyBearModulus} {program : List Trace.RVPooledProgramEntry}
    {before : RV.State} {callerAddresses ordinaryAddresses : List (BitVec 32)}
    {cells : List Trace.Cell} (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVMixedMemoryInputs data program before callerAddresses ordinaryAddresses cells) :
    RVMixedMemoryEffects data before cells :=
  Proofs.rv_mixed_memory_effects accepted inputs

/-- RV sibling of `worker_schedule_soundness`. -/
theorem rv_worker_schedule_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} (accepted : RVRequestChecks data)
    (inputs : RVRequestInputs data before addresses) : RVWorkerSchedule data :=
  Proofs.rv_worker_schedule hp clockInverse accepted inputs
    (Proofs.rv_request_binding_checks hp clockInverse pcInverse accepted inputs)

/-- RV sibling of `request_window_soundness`. -/
theorem rv_request_window_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    RequestWindowBinding data.callers data.workers lower upper :=
  Proofs.rv_request_windows hp clockInverse pcInverse accepted inputs first last pastZero

/-- RV sibling of `request_hash_window_soundness`, with the delegate link in `HashSpan.RVResult`. -/
theorem rv_request_hash_window_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    (wordInverse : 64 * (-31457280 : ZMod p) = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    {cells : List Trace.Cell} {span : HashSpan} {lower upper : Nat}
    (accepted : RVRequestAccepted data) (program : RVRequestInputs data before addresses)
    (inputs : span.RVRequestWindowInputs data.workers before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    span.RVRequestWindowResult data.callers data.workers before cells lower upper :=
  Proofs.rv_bind_hash_window hp wordInverse byteInverse accepted.workers inputs aligned
    (Proofs.rv_request_windows (by norm_num [Trace.timestampBase]; omega) clockInverse pcInverse
      accepted.toRVRequestChecks program first last pastZero)

end Airbender.Delegation.Caller
