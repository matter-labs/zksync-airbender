import Airbender.Proofs.UnifiedReduced.MixedComposition
import Airbender.Proofs.UnifiedReduced.Composition
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.SharedSpans
import Airbender.Proofs.UnifiedReduced.RequestWindows
import Airbender.Proofs.Delegation.RequestHashWindows

namespace Airbender.UnifiedReduced

/-- Standard instructions and project TRIADD/XORROT retire in one trace, with
    their original public Sail decoding and shared initialized history. Final
    PC/cells agree with native terminal tokens; readonly ROM uses actual public
    bytes rather than zero shadow slots. `Mixed.Inputs` contains only the shared
    public boot/configuration/profile conditions. No row reads, bounds, decoded
    results or expected outputs are assumptions. Delegation callers are outside
    this registry. -/
theorem Mixed.execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Mixed.Inputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Mixed.Step program) trace initial cells (Trace.ROMView.token initial) :=
  Mixed.Proofs.trace_execution hp clockInverse byteInverse inputs accepted decoded

/-- Every admitted native row, in its history-derived order, executes the original
    Sail instruction fetched from public bytes. The final PC and all tracked
    cells match the declared terminal tokens; readonly ROM uses its public bytes.
    `ExecutionInputs` lists public boot/configuration/profile conditions. Reads,
    selectors and word bounds are proved internally from the imported artifact,
    modeled tables and logical matching. No terminal-PC normalization is needed. -/
theorem execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : ExecutionInputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Step program) trace initial cells (Trace.ROMView.token initial) :=
  Proofs.trace_execution hp clockInverse byteInverse inputs accepted decoded

open Airbender.Reference.RiscV

/-- Unified standard/custom instructions, callers and workers share one public
    initialized architecture. Reads, word/address bounds, x0 values and worker
    references are derived through Clean history and actual Sail transfers.
    Whole retirement, native ROM shadows and hash spans remain separate. -/
theorem Caller.mixed_memory_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells) : Caller.MixedMemoryEffects data before cells :=
  Caller.Proofs.mixed_memory_effects accepted inputs

/-- Complete BLAKE G, extended BLAKE and Keccak spans reach their pinned
    references in one actual shared terminal state. The empty ordinary registry
    establishes caller-only rows. Public initialization, mode/span-size ABI,
    modeled tables and logical matching remain visible in `SharedSpanInputs`.
    Worker boundaries, all ranges and intermediate controls are derived.
    This is a memory-effect claim; PC retirement, arbitrary mixed-ISA span
    segmentation and unissued-worker exclusion remain separate. -/
theorem Caller.shared_span_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan}
    (accepted : Caller.MixedMemoryAccepted data [])
    (inputs : Caller.SharedSpanInputs data before addresses cells span) :
    Caller.SharedSpanEffects data before cells span :=
  Caller.Proofs.shared_span_effects hp clockInverse accepted inputs

/-- Unified caller spans match the complete native worker rows between the
    same instruction-boundary cuts. Counts and unique native slots are derived;
    zero-clock surplus effects stay before the cut rather than being excluded. -/
theorem Caller.request_window_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : Caller.RequestChecks data) (inputs : Caller.RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper :=
  Caller.Proofs.request_windows hp clockInverse accepted inputs first last pastZero

/-- Unified caller requests and the complete hash reference bind the same native
    window. Public worker initialization, mode/count ABI and worker-only matching
    remain visible; caller control preparation and joint retirement are separate. -/
theorem Caller.request_hash_window_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (wordInverse : 64 * (-31457280 : ZMod p) = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : Caller.RequestChecks data) (workers : Delegation.MemoryAccepted data.workers)
    (program : Caller.RequestInputs data before addresses)
    (inputs : span.RequestWindowInputs data.workers before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    span.RequestWindowResult data.callers data.workers before cells lower upper :=
  Delegation.Caller.Proofs.bind_hash_window hp wordInverse byteInverse workers inputs aligned
    (Caller.Proofs.request_windows (by norm_num [Trace.timestampBase]; omega) clockInverse
      accepted program first last pastZero)

end Airbender.UnifiedReduced
