import Airbender.Proofs.Delegation.Schedule
import Airbender.Proofs.Delegation.RequestHashWindows
import Airbender.Proofs.Delegation.MixedMemory
import Airbender.Proofs.Delegation.SharedSpans
import Airbender.Proofs.Delegation.SharedOperations
import Airbender.Proofs.Delegation.SharedMemory
import Airbender.Proofs.Delegation.RequestEffects
import Airbender.Proofs.Delegation.RequestTrace
import Airbender.Proofs.Delegation.Decoder
import Airbender.Review.Trace.Delegation.Theorems

namespace Airbender.Delegation.Caller

/-- Bind public caller instructions to actual worker rows through the native
    request permutation. Initialized machine clocks prove invocation bounds
    and write-offset room for the entire worker pool. Zero-clock workers remain
    an explicit gap; architectural caller/worker memory composition is separate. -/
theorem requests_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} (accepted : RequestAccepted data)
    (inputs : RequestInputs data before addresses) : RequestBinding data before :=
  Proofs.request_binding hp clockInverse pcInverse accepted inputs

/-- Connect caller requests to the worker pool's actual Sail memory effects.
    Public initialization and logical native permutations supply the inputs;
    invocation bounds and write-offset room come from the machine state path.
    This does not claim whole-machine execution or close zero-clock fulfillment. -/
theorem request_memory_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : RequestAccepted data) (inputs : RequestMemoryInputs data before addresses cells) :
    RequestExecution data before cells :=
  Proofs.request_memory_execution hp clockInverse pcInverse accepted inputs

/-- Decoded callers are linked to actual initialized workers whose native port
    effects match the named bigint/Clean hash references. All worker bounds and
    timestamp room are derived. Public initialization, modeled tables and the
    visible extended-round ABI remain; mixed architectural memory and span
    segmentation are separate. BabyBear is explicit because bigint's current
    multiplication proof uses that artifact's coefficients. -/
theorem operation_soundness
    {data : RequestTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {cells : List Trace.Cell} (accepted : RequestAccepted data)
    (inputs : RequestOperationInputs data before addresses cells) :
    RequestOperationEffects data before cells :=
  Proofs.request_operation_effects accepted inputs

/-- Caller and worker GPR/RAM transfers execute in one initialized Sail history.
    The virtual CSR port stays in its own request permutation. Shared matching
    proves the caller's canonical x0 source and every worker address bound;
    no worker-only memory permutation or expected read is assumed. This claim
    admits caller machine rows only; operation/span and mixed ISA composition
    remain separate obligations. -/
theorem shared_memory_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedMemoryInputs data before addresses cells) :
    SharedMemoryEffects data before cells :=
  Proofs.shared_memory_execution hp clockInverse pcInverse accepted inputs

/-- Caller and worker accesses share initialization, memory matching and actual
    Sail transfers. The same history derives all operand/pointer/result bounds
    and connects native port values to the four existing operation references.
    Only modeled tables and the extended-round ABI are added to public inputs;
    span ABI and standard/custom machine composition remain open. -/
theorem shared_operation_soundness
    {data : RequestTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedOperationInputs data before addresses cells) :
    SharedOperationEffects data before cells :=
  Proofs.shared_operation_effects accepted inputs

/-- A complete existing hash span reaches its reference result in the same
    state that realizes every shared terminal token. Worker memory matching,
    initialization, clock room and control-cell coverage are derived from the
    caller/worker pool. Only public mode/control and the existing span-size ABI
    boundary remain; mixed ISA composition and zero-clock exclusion stay open. -/
theorem shared_span_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : HashSpan}
    (accepted : SharedMemoryAccepted data) (inputs : SharedSpanInputs data before addresses cells span) :
    SharedSpanEffects data before cells span :=
  Proofs.shared_span_effects hp inverse accepted inputs

/-- Ordinary six-family instructions and delegation workers share initialized
    architectural memory. Actual public decoding supplies x0 preservation;
    shared history supplies every word/address bound and actual Sail transfer.
    Worker effects use the existing references. Mixed instruction retirement,
    span segmentation and the flagged zero-clock gap remain separate. -/
theorem mixed_memory_soundness
    {data : RequestTrace babyBearModulus} {program : List Trace.PooledProgramEntry}
    {before : Reference.RiscV.Sail.State} {callerAddresses ordinaryAddresses : List (BitVec 32)}
    {cells : List Trace.Cell} (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program before callerAddresses ordinaryAddresses cells) :
    MixedMemoryEffects data before cells :=
  Proofs.mixed_memory_effects accepted inputs

/-- Request matching places exactly one worker inside each caller's native
    four-tick cycle. Every live worker belongs to one caller; no instruction
    starts inside that cycle. Zero-clock workers are classified as unissued,
    so this claim does not hide the flagged fulfillment gap. -/
theorem worker_schedule_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} (accepted : RequestChecks data)
    (inputs : RequestInputs data before addresses) : WorkerSchedule data :=
  Proofs.worker_schedule hp clockInverse accepted inputs
    (Proofs.request_binding_checks hp clockInverse pcInverse accepted inputs)

/-- Instruction-boundary cuts select exactly the callers issuing the native
    worker window. Counts, full CSR tokens and unique slots are derived.
    Cuts follow clock two; surplus zero-clock effects remain in the prefix. -/
theorem request_window_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    RequestWindowBinding data.callers data.workers lower upper :=
  Proofs.request_windows hp clockInverse pcInverse accepted inputs first last pastZero

/-- The same selected workers bind actual caller requests and a complete pinned
    hash reference at derived Sail cut states. The existing public worker-window
    ABI and worker-only matching remain explicit; mixed retirement is separate. -/
theorem request_hash_window_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    (wordInverse : 64 * (-31457280 : ZMod p) = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {cells : List Trace.Cell} {span : HashSpan} {lower upper : Nat}
    (accepted : RequestAccepted data) (program : RequestInputs data before addresses)
    (inputs : span.RequestWindowInputs data.workers before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    span.RequestWindowResult data.callers data.workers before cells lower upper :=
  Proofs.bind_hash_window hp wordInverse byteInverse accepted.workers inputs aligned
    (Proofs.request_windows (by norm_num [Trace.timestampBase]; omega) clockInverse pcInverse
      accepted.toRequestChecks program first last pastZero)

end Airbender.Delegation.Caller
