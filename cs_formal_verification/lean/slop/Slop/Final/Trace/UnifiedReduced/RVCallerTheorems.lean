module
public import Human.Trace.UnifiedReduced.RVCallerTheorems
public import Slop.UnifiedReduced.RVCaller.RequestWindows
public import Slop.UnifiedReduced.RVCaller.MixedMemory
public import Slop.UnifiedReduced.RVCaller.SharedSpans
public import Slop.Delegation.RVRequestHashWindows
public import Slop.UnifiedReduced.RVCaller.WindowProjection
public import Slop.UnifiedReduced.RVCaller.JointHashWindows
public import Slop.UnifiedReduced.RVCaller.MixedWindowProjection
public import Slop.UnifiedReduced.RVCaller.ControlPreparation
public import Slop.UnifiedReduced.RVCaller.PreparedRoundWindows
public import Slop.UnifiedReduced.RVCaller.CallerCycles
public import Slop.Final.Generic.Trace.UnifiedReduced.RVCallerTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.UnifiedReduced

/-- Unified caller spans match the complete native worker rows between the same instruction-boundary cuts, with callers
    read from the RV program table. -/
private theorem Caller.rv_request_window_soundness_generic : Caller.RVRequestWindowSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before addresses accepted inputs lower upper first last pastZero
  exact Caller.Proofs.rv_request_windows hp clockInverse accepted inputs first last pastZero

theorem Caller.rv_request_window_soundness : Caller.RVRequestWindowSoundnessClaim := by babybear_instance Caller.rv_request_window_soundness_generic

/-- Unified instructions, callers and workers share one public initialized RV architecture: reads, bounds, x0 values
    and worker references are derived, and every issued worker and instruction cycle has actual RV states. -/
theorem Caller.rv_mixed_memory_soundness : Caller.RVMixedMemorySoundnessClaim := by
  intro data program before ca oa cells accepted inputs
  exact Caller.Proofs.rv_mixed_memory_effects accepted inputs

/-- Complete G, extended-BLAKE and Keccak spans reach their RV references (delegate link included) in one actual
    shared terminal RV state. -/
private theorem Caller.rv_shared_span_soundness_generic : Caller.RVSharedSpanSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before addresses cells span accepted inputs
  exact Caller.Proofs.rv_shared_span_effects hp clockInverse accepted inputs

theorem Caller.rv_shared_span_soundness : Caller.RVSharedSpanSoundnessClaim := by babybear_instance Caller.rv_shared_span_soundness_generic

/-- Unified caller requests from the RV caller table and the complete RV hash reference (delegate link included) bind
    the same native window. -/
private theorem Caller.rv_request_hash_window_soundness_generic : Caller.RVRequestHashWindowSoundnessClaimGeneric := by
  intro p _ hp clockInverse wordInverse byteInverse data before addresses cells span lower upper accepted workers
    program inputs aligned first last pastZero
  exact Delegation.Caller.Proofs.rv_bind_hash_window hp wordInverse byteInverse workers inputs aligned
    (Caller.Proofs.rv_request_windows (by norm_num [Trace.timestampBase]; omega) clockInverse
      accepted program first last pastZero)

theorem Caller.rv_request_hash_window_soundness : Caller.RVRequestHashWindowSoundnessClaim := by babybear_instance Caller.rv_request_hash_window_soundness_generic

/-- Complete instruction and worker rows between public aligned cuts execute in one initialized RV history, with
    actual cut RV states and native boundaries. -/
private theorem Caller.rv_mixed_window_soundness_generic : Caller.RVMixedWindowSoundnessClaimGeneric := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells accepted inputs lower upper first last
    pastZero ordered
  exact Caller.Proofs.rv_mixed_window_execution hp clockInverse rotationInverse accepted inputs first last pastZero
    ordered

theorem Caller.rv_mixed_window_soundness : Caller.RVMixedWindowSoundnessClaim := by babybear_instance Caller.rv_mixed_window_soundness_generic

/-- Projected worker memory retains the joint RV states and native timestamps. -/
private theorem Caller.rv_window_projection_soundness_generic : Caller.RVWindowProjectionSoundnessClaimGeneric := by
  intro p _ hp clockInverse rotationInverse data before ca oa cells accepted inputs lower upper first last positive
    ordered
  exact Caller.Proofs.rv_projected_window hp clockInverse rotationInverse accepted inputs first last positive ordered

theorem Caller.rv_window_projection_soundness : Caller.RVWindowProjectionSoundnessClaim := by babybear_instance Caller.rv_window_projection_soundness_generic

/-- Two native windows and their gap form one actual RV memory execution from public initialization. -/
private theorem Caller.rv_mixed_window_chain_soundness_generic : Caller.RVMixedWindowChainSoundnessClaimGeneric := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells a b c d accepted inputs aa ba ca' da
    positive ab bc cd
  exact Caller.Proofs.rv_mixed_window_chain hp clockInverse rotationInverse accepted inputs aa ba ca' da positive ab bc cd

theorem Caller.rv_mixed_window_chain_soundness : Caller.RVMixedWindowChainSoundnessClaim := by babybear_instance Caller.rv_mixed_window_chain_soundness_generic

/-- An ordered finite list of native windows and gaps executes continuously in one RV history. -/
private theorem Caller.rv_mixed_window_sequence_soundness_generic : Caller.RVMixedWindowSequenceSoundnessClaimGeneric := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells cut windows accepted inputs first positive
    ordered
  exact Caller.Proofs.rv_mixed_window_sequence hp clockInverse rotationInverse accepted inputs first positive ordered

theorem Caller.rv_mixed_window_sequence_soundness : Caller.RVMixedWindowSequenceSoundnessClaim := by babybear_instance Caller.rv_mixed_window_sequence_soundness_generic

/-- Caller-only hash windows reach their complete RV reference (delegate link included) at the actual joint cut
    RV states. -/
private theorem Caller.rv_joint_hash_window_soundness_generic : Caller.RVJointHashWindowSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before addresses cells span lower upper accepted inputs first last positive ordered
  exact Caller.Proofs.rv_joint_hash_window hp clockInverse accepted inputs first last positive ordered

theorem Caller.rv_joint_hash_window_soundness : Caller.RVJointHashWindowSoundnessClaim := by babybear_instance Caller.rv_joint_hash_window_soundness_generic

/-- Accepted state matching counts every instruction between the public cuts (callers from the RV caller table). -/
private theorem Caller.rv_window_schedule_soundness_generic : Caller.RVWindowScheduleSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before addresses accepted inputs lower upper first last positive ordered afterInitial
    beforeTerminal duration
  exact Caller.Proofs.rv_caller_window_schedule hp clockInverse accepted inputs first last positive ordered afterInitial
    beforeTerminal duration

theorem Caller.rv_window_schedule_soundness : Caller.RVWindowScheduleSoundnessClaim := by babybear_instance Caller.rv_window_schedule_soundness_generic

/-- Caller regions within mixed RV history derive worker matching and retained boundary images at the actual cut
    states. -/
private theorem Caller.rv_mixed_window_projection_soundness_generic : Caller.RVMixedWindowProjectionSoundnessClaimGeneric := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells accepted inputs lower upper first last
    positive ordered afterInitial beforeTerminal duration
  exact Caller.Proofs.rv_mixed_projected_window hp clockInverse rotationInverse accepted inputs first last positive
    ordered afterInitial beforeTerminal duration

theorem Caller.rv_mixed_window_projection_soundness : Caller.RVMixedWindowProjectionSoundnessClaim := by babybear_instance Caller.rv_mixed_window_projection_soundness_generic

/-- Public ADDI-from-x0/LUI decoding (`RV.decode` of the RV program table) and accepted native writes prepare the actual
    control in the RV state at the prepared cut. -/
private theorem Caller.rv_control_preparation_soundness_generic : Caller.RVControlPreparationSoundnessClaimGeneric := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells cut register literal accepted inputs scope
    nonzero aligned
  exact Caller.Proofs.rv_control_preparation hp clockInverse rotationInverse accepted inputs scope nonzero aligned

theorem Caller.rv_control_preparation_soundness : Caller.RVControlPreparationSoundnessClaim := by babybear_instance Caller.rv_control_preparation_soundness_generic

/-- Two prepared controls use the same actual RV states and intervening native history. -/
private theorem Caller.rv_control_preparation_window_soundness_generic : Caller.RVControlPreparationWindowSoundnessClaimGeneric := by
  intro p _ hp clockInverse rotationInverse data program before ca oa cells lower upper firstRegister lastRegister
    firstLiteral lastLiteral accepted inputs firstScope lastScope firstNonzero lastNonzero first last ordered
  exact Caller.Proofs.rv_control_preparation_window hp clockInverse rotationInverse accepted inputs firstScope lastScope
    firstNonzero lastNonzero first last ordered

theorem Caller.rv_control_preparation_window_soundness : Caller.RVControlPreparationWindowSoundnessClaim := by babybear_instance Caller.rv_control_preparation_window_soundness_generic

/-- Public sequential RV code identifies a caller region; native matching derives its worker family, counts and
    slots. -/
private theorem Caller.rv_program_window_schedule_soundness_generic : Caller.RVProgramWindowScheduleSoundnessClaimGeneric := by
  intro p _ hp clockInverse data program before ca oa family lower upper accepted publicProgram ordinaryProgram registry
    region first last positive ordered afterInitial beforeTerminal
  exact Caller.Proofs.rv_program_caller_window hp clockInverse accepted publicProgram ordinaryProgram registry region
    first last positive ordered afterInitial beforeTerminal

theorem Caller.rv_program_window_schedule_soundness : Caller.RVProgramWindowScheduleSoundnessClaim := by babybear_instance Caller.rv_program_window_schedule_soundness_generic

/-- Complete G and Keccak RV references (delegate link included) reach the actual mixed-history cut RV states after
    public RV literal preparation. -/
private theorem Caller.rv_prepared_hash_window_soundness_generic : Caller.RVPreparedHashWindowSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before ca oa cells program span lower upper accepted inputs first last
  exact Caller.Proofs.rv_prepared_hash_window hp clockInverse accepted inputs first last

theorem Caller.rv_prepared_hash_window_soundness : Caller.RVPreparedHashWindowSoundnessClaim := by babybear_instance Caller.rv_prepared_hash_window_soundness_generic

/-- Two complete prepared G/Keccak RV references compose through one continuous RV history. -/
private theorem Caller.rv_prepared_hash_chain_soundness_generic : Caller.RVPreparedHashChainSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before ca oa cells program firstSpan secondSpan a b c d accepted firstInputs
    secondInputs aa ba ca' da gap
  exact Caller.Proofs.rv_prepared_hash_chain hp clockInverse accepted firstInputs secondInputs aa ba ca' da gap

theorem Caller.rv_prepared_hash_chain_soundness : Caller.RVPreparedHashChainSoundnessClaim := by babybear_instance Caller.rv_prepared_hash_chain_soundness_generic

/-- A nonempty ordered list of complete prepared G/Keccak RV references shares one continuous RV history. -/
private theorem Caller.rv_prepared_hash_sequence_soundness_generic : Caller.RVPreparedHashSequenceSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before ca oa cells program first rest accepted firstInputs restInputs ordered
  exact Caller.Proofs.rv_prepared_hash_sequence hp clockInverse accepted firstInputs restInputs ordered

theorem Caller.rv_prepared_hash_sequence_soundness : Caller.RVPreparedHashSequenceSoundnessClaim := by babybear_instance Caller.rv_prepared_hash_sequence_soundness_generic

/-- Public RV LUI preparation and raw joint matching derive exclusive masks within one caller region. -/
private theorem Caller.rv_prepared_round_region_masks_soundness_generic : Caller.RVPreparedRoundRegionMasksSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before ca oa cells program regions region accepted inputs scope
  exact Caller.Proofs.rv_prepared_round_region_masks hp clockInverse accepted inputs scope

theorem Caller.rv_prepared_round_region_masks_soundness : Caller.RVPreparedRoundRegionMasksSoundnessClaim := by babybear_instance Caller.rv_prepared_round_region_masks_soundness_generic

/-- Complete prepared G, extended-BLAKE and Keccak RV references share one continuous RV memory execution. -/
private theorem Caller.rv_prepared_protocol_sequence_soundness_generic : Caller.RVPreparedProtocolSequenceSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before ca oa cells program regions first rest accepted inputs scopes ordered
  exact Caller.Proofs.rv_prepared_protocol_sequence hp clockInverse accepted inputs scopes ordered

theorem Caller.rv_prepared_protocol_sequence_soundness : Caller.RVPreparedProtocolSequenceSoundnessClaim := by babybear_instance Caller.rv_prepared_protocol_sequence_soundness_generic

/-- Public RV LUI preparation and native matching derive all extended-BLAKE masks. -/
private theorem Caller.rv_prepared_round_masks_soundness_generic : Caller.RVPreparedRoundMasksSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before ca oa cells program flags lower accepted inputs first
  exact Caller.Proofs.rv_prepared_round_masks hp clockInverse accepted inputs first

theorem Caller.rv_prepared_round_masks_soundness : Caller.RVPreparedRoundMasksSoundnessClaim := by babybear_instance Caller.rv_prepared_round_masks_soundness_generic

/-- Complete extended-BLAKE compression (delegate link included) reaches the actual prepared mixed-history cut RV
    states. -/
private theorem Caller.rv_prepared_round_window_soundness_generic : Caller.RVPreparedRoundWindowSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before ca oa cells program flags lower upper accepted inputs first last
  exact Caller.Proofs.rv_prepared_round_window hp clockInverse accepted inputs first last

theorem Caller.rv_prepared_round_window_soundness : Caller.RVPreparedRoundWindowSoundnessClaim := by babybear_instance Caller.rv_prepared_round_window_soundness_generic

/-- Public RV caller regions derive selected worker families and complete call counts for all three references in one
    continuous prepared RV history. -/
private theorem Caller.rv_program_prepared_protocol_sequence_soundness_generic :
    Caller.RVProgramPreparedProtocolSequenceSoundnessClaimGeneric := by
  intro p _ hp clockInverse data before ca oa cells program regions first rest accepted inputs registry scopes ordered
  exact Caller.Proofs.rv_program_prepared_protocol_sequence hp clockInverse accepted inputs registry scopes ordered

theorem Caller.rv_program_prepared_protocol_sequence_soundness : Airbender.UnifiedReduced.Caller.RVProgramPreparedProtocolSequenceSoundnessClaim := by babybear_instance Caller.rv_program_prepared_protocol_sequence_soundness_generic

/-- Actual caller fetch from the RV program table, issued-worker references and the spec's PC retirement use one
    shared RV history; each caller's `RV.step` at its pre-state is `RV.exec` of its decoded `.delegate k`. -/
theorem Caller.rv_caller_cycles_soundness : Caller.RVCallerCyclesSoundnessClaim := by
  intro data program initial ca oa cells accepted inputs started
  exact Caller.Proofs.rv_caller_cycles accepted inputs started

/-- The prepared extended-round scope derives masks before constructing the same actual RV caller cycles. -/
theorem Caller.rv_prepared_round_cycles_soundness : Caller.RVPreparedRoundCyclesSoundnessClaim := by
  intro data program initial ca oa cells flags lower accepted inputs first started
  exact Caller.Proofs.rv_prepared_round_caller_cycles accepted inputs first started

end Airbender.UnifiedReduced
