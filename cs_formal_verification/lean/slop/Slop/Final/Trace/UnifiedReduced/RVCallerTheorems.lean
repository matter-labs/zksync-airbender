import Human.Trace.UnifiedReduced.RVCallerTheorems
import Slop.UnifiedReduced.RVCaller.RequestWindows
import Slop.UnifiedReduced.RVCaller.MixedMemory
import Slop.UnifiedReduced.RVCaller.SharedSpans
import Slop.UnifiedReduced.RVCaller.RequestHashWindows
import Slop.UnifiedReduced.RVCaller.WindowProjection

namespace Airbender.UnifiedReduced

/-- Unified caller spans match the complete native worker rows between the same instruction-boundary cuts, with callers
    read from the RV program table. -/
theorem Caller.rv_request_window_soundness : Caller.RVRequestWindowSoundnessClaim := by
  intro p _ hp clockInverse data before addresses accepted inputs lower upper first last pastZero
  exact Caller.Proofs.rv_request_windows hp clockInverse accepted inputs first last pastZero

/-- Unified instructions, callers and workers share one public initialized RV architecture: reads, bounds, x0 values
    and worker references are derived, and every issued worker and instruction cycle has actual RV states. -/
theorem Caller.rv_mixed_memory_soundness : Caller.RVMixedMemorySoundnessClaim := by
  intro data program before ca oa cells accepted inputs
  exact Caller.Proofs.rv_mixed_memory_effects accepted inputs

/-- Complete G, extended-BLAKE and Keccak spans reach their RV references (delegate link included) in one actual
    shared terminal RV state. -/
theorem Caller.rv_shared_span_soundness : Caller.RVSharedSpanSoundnessClaim := by
  intro p _ hp clockInverse data before addresses cells span accepted inputs
  exact Caller.Proofs.rv_shared_span_effects hp clockInverse accepted inputs

/-- Unified caller requests from the RV caller table and the complete RV hash reference (delegate link included) bind
    the same native window. -/
theorem Caller.rv_request_hash_window_soundness : Caller.RVRequestHashWindowSoundnessClaim := by
  intro p _ hp clockInverse wordInverse byteInverse data before addresses cells span lower upper accepted workers
    program inputs aligned first last pastZero
  exact Caller.Proofs.rv_bind_hash_window hp wordInverse byteInverse workers inputs aligned
    (Caller.Proofs.rv_request_windows (by norm_num [Trace.timestampBase]; omega) clockInverse
      accepted program first last pastZero)

/-- Complete instruction and worker rows between public aligned cuts execute in one initialized RV history, with
    actual cut RV states and native boundaries. -/
theorem Caller.rv_mixed_window_soundness : Caller.RVMixedWindowSoundnessClaim := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells accepted inputs lower upper first last
    pastZero ordered
  exact Caller.Proofs.rv_mixed_window_execution hp clockInverse rotationInverse accepted inputs first last pastZero
    ordered

/-- Projected worker memory retains the joint RV states and native timestamps. -/
theorem Caller.rv_window_projection_soundness : Caller.RVWindowProjectionSoundnessClaim := by
  intro p _ hp clockInverse rotationInverse data before ca oa cells accepted inputs lower upper first last positive
    ordered
  exact Caller.Proofs.rv_projected_window hp clockInverse rotationInverse accepted inputs first last positive ordered

/-- Two native windows and their gap form one actual RV memory execution from public initialization. -/
theorem Caller.rv_mixed_window_chain_soundness : Caller.RVMixedWindowChainSoundnessClaim := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells a b c d accepted inputs aa ba ca' da
    positive ab bc cd
  exact Caller.Proofs.rv_mixed_window_chain hp clockInverse rotationInverse accepted inputs aa ba ca' da positive ab bc cd

/-- An ordered finite list of native windows and gaps executes continuously in one RV history. -/
theorem Caller.rv_mixed_window_sequence_soundness : Caller.RVMixedWindowSequenceSoundnessClaim := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells cut windows accepted inputs first positive
    ordered
  exact Caller.Proofs.rv_mixed_window_sequence hp clockInverse rotationInverse accepted inputs first positive ordered

end Airbender.UnifiedReduced
