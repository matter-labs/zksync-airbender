import Human.Trace.UnifiedReduced.RVCallerTheorems
import Slop.UnifiedReduced.RVCaller.RequestWindows
import Slop.UnifiedReduced.RVCaller.MixedMemory
import Slop.UnifiedReduced.RVCaller.SharedSpans
import Slop.UnifiedReduced.RVCaller.RequestHashWindows
import Slop.UnifiedReduced.RVCaller.WindowProjection
import Slop.UnifiedReduced.RVCaller.JointHashWindows
import Slop.UnifiedReduced.RVCaller.MixedWindowProjection
import Slop.UnifiedReduced.RVCaller.ControlPreparation
import Slop.UnifiedReduced.RVCaller.PreparedRoundWindows

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

/-- Caller-only hash windows reach their complete RV reference (delegate link included) at the actual joint cut
    RV states. -/
theorem Caller.rv_joint_hash_window_soundness : Caller.RVJointHashWindowSoundnessClaim := by
  intro p _ hp clockInverse data before addresses cells span lower upper accepted inputs first last positive ordered
  exact Caller.Proofs.rv_joint_hash_window hp clockInverse accepted inputs first last positive ordered

/-- Accepted state matching counts every instruction between the public cuts (callers from the RV caller table). -/
theorem Caller.rv_window_schedule_soundness : Caller.RVWindowScheduleSoundnessClaim := by
  intro p _ hp clockInverse data before addresses accepted inputs lower upper first last positive ordered afterInitial
    beforeTerminal duration
  exact Caller.Proofs.rv_caller_window_schedule hp clockInverse accepted inputs first last positive ordered afterInitial
    beforeTerminal duration

/-- Caller regions within mixed RV history derive worker matching and retained boundary images at the actual cut
    states. -/
theorem Caller.rv_mixed_window_projection_soundness : Caller.RVMixedWindowProjectionSoundnessClaim := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells accepted inputs lower upper first last
    positive ordered afterInitial beforeTerminal duration
  exact Caller.Proofs.rv_mixed_projected_window hp clockInverse rotationInverse accepted inputs first last positive
    ordered afterInitial beforeTerminal duration

/-- Public ADDI-from-x0/LUI decoding (`RV.decode` of the RV program table) and accepted native writes prepare the actual
    control in the RV state at the prepared cut. -/
theorem Caller.rv_control_preparation_soundness : Caller.RVControlPreparationSoundnessClaim := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells cut register literal accepted inputs scope
    nonzero aligned
  exact Caller.Proofs.rv_control_preparation hp clockInverse rotationInverse accepted inputs scope nonzero aligned

/-- Two prepared controls use the same actual RV states and intervening native history. -/
theorem Caller.rv_control_preparation_window_soundness : Caller.RVControlPreparationWindowSoundnessClaim := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells lower upper firstRegister lastRegister
    firstLiteral lastLiteral accepted inputs firstScope lastScope firstNonzero lastNonzero first last ordered
  exact Caller.Proofs.rv_control_preparation_window hp clockInverse rotationInverse accepted inputs firstScope lastScope
    firstNonzero lastNonzero first last ordered

/-- Public sequential RV code identifies a caller region; native matching derives its worker family, counts and
    slots. -/
theorem Caller.rv_program_window_schedule_soundness : Caller.RVProgramWindowScheduleSoundnessClaim := by
  intro p _ hp clockInverse data program before ca oa family lower upper accepted publicProgram ordinaryProgram registry
    region first last positive ordered afterInitial beforeTerminal
  exact Caller.Proofs.rv_program_caller_window hp clockInverse accepted publicProgram ordinaryProgram registry region
    first last positive ordered afterInitial beforeTerminal

/-- Complete G and Keccak RV references (delegate link included) reach the actual mixed-history cut RV states after
    public RV literal preparation. -/
theorem Caller.rv_prepared_hash_window_soundness : Caller.RVPreparedHashWindowSoundnessClaim := by
  intro p _ hp clockInverse data before ca oa cells program span lower upper accepted inputs first last
  exact Caller.Proofs.rv_prepared_hash_window hp clockInverse accepted inputs first last

/-- Two complete prepared G/Keccak RV references compose through one continuous RV history. -/
theorem Caller.rv_prepared_hash_chain_soundness : Caller.RVPreparedHashChainSoundnessClaim := by
  intro p _ hp clockInverse data before ca oa cells program firstSpan secondSpan a b c d accepted firstInputs
    secondInputs aa ba ca' da gap
  exact Caller.Proofs.rv_prepared_hash_chain hp clockInverse accepted firstInputs secondInputs aa ba ca' da gap

/-- A nonempty ordered list of complete prepared G/Keccak RV references shares one continuous RV history. -/
theorem Caller.rv_prepared_hash_sequence_soundness : Caller.RVPreparedHashSequenceSoundnessClaim := by
  intro p _ hp clockInverse data before ca oa cells program first rest accepted firstInputs restInputs ordered
  exact Caller.Proofs.rv_prepared_hash_sequence hp clockInverse accepted firstInputs restInputs ordered

/-- Public RV LUI preparation and raw joint matching derive exclusive masks within one caller region. -/
theorem Caller.rv_prepared_round_region_masks_soundness : Caller.RVPreparedRoundRegionMasksSoundnessClaim := by
  intro p _ hp clockInverse data before ca oa cells program regions region accepted inputs scope
  exact Caller.Proofs.rv_prepared_round_region_masks hp clockInverse accepted inputs scope

/-- Complete prepared G, extended-BLAKE and Keccak RV references share one continuous RV memory execution. -/
theorem Caller.rv_prepared_protocol_sequence_soundness : Caller.RVPreparedProtocolSequenceSoundnessClaim := by
  intro p _ hp clockInverse data before ca oa cells program regions first rest accepted inputs scopes ordered
  exact Caller.Proofs.rv_prepared_protocol_sequence hp clockInverse accepted inputs scopes ordered

/-- Public RV LUI preparation and native matching derive all extended-BLAKE masks. -/
theorem Caller.rv_prepared_round_masks_soundness : Caller.RVPreparedRoundMasksSoundnessClaim := by
  intro p _ hp clockInverse data before ca oa cells program flags lower accepted inputs first
  exact Caller.Proofs.rv_prepared_round_masks hp clockInverse accepted inputs first

/-- Complete extended-BLAKE compression (delegate link included) reaches the actual prepared mixed-history cut RV
    states. -/
theorem Caller.rv_prepared_round_window_soundness : Caller.RVPreparedRoundWindowSoundnessClaim := by
  intro p _ hp clockInverse data before ca oa cells program flags lower upper accepted inputs first last
  exact Caller.Proofs.rv_prepared_round_window hp clockInverse accepted inputs first last

/-- Public RV caller regions derive selected worker families and complete call counts for all three references in one
    continuous prepared RV history. -/
theorem Caller.rv_program_prepared_protocol_sequence_soundness :
    Caller.RVProgramPreparedProtocolSequenceSoundnessClaim := by
  intro p _ hp clockInverse data before ca oa cells program regions first rest accepted inputs registry scopes ordered
  exact Caller.Proofs.rv_program_prepared_protocol_sequence hp clockInverse accepted inputs registry scopes ordered

end Airbender.UnifiedReduced
