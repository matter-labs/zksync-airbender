-- Each final theorem (slop/Slop/Final) proves the statement of the same name in human/ (UpperCamelCase).
import Slop.Final.Circuits.AddSub.RVTheorems
import Slop.Final.Circuits.Bigint.RVTheorems
import Slop.Final.Circuits.Blake2G.Theorems
import Slop.Final.Circuits.InitsTeardowns.Theorems
import Slop.Final.Circuits.JumpBranchSlt.RVTheorems
import Slop.Final.Circuits.MulDiv.RVTheorems
import Slop.Final.Circuits.ShiftBinop.RVTheorems
import Slop.Final.Circuits.SubwordMemory.RVTheorems
import Slop.Final.Circuits.WordMemory.RVTheorems
import Slop.Final.Trace.UnifiedReduced.RVTheorems
import Slop.Final.Trace.RVSoundness
import Slop.Final.Helpers.Context.PCState.Theorems
import Slop.Final.ISA.Theorems
import Slop.Final.ISA.DelegationRuns
import Slop.Final.ISA.Vectors
import Slop.Final.Trace.Delegation.RVTheorems
import Slop.Final.Trace.Families.AddSub.RVTheorems
import Slop.Final.Trace.Families.JumpBranchSlt.RVTheorems
import Slop.Final.Trace.Families.MulDiv.RVTheorems
import Slop.Final.Trace.Families.ShiftBinop.RVTheorems
import Slop.Final.Trace.Families.SubwordMemory.RVTheorems
import Slop.Final.Trace.ZeroTimestamp
import Slop.Final.Trace.WritesRangeChecked
import Slop.Final.Trace.TeardownBounds
import Slop.Final.Trace.Workers.Bigint.RVTheorems
import Slop.Final.Trace.Workers.Blake2G.RVTheorems
import Slop.Final.Trace.Workers.Blake2Round.RVTheorems
import Slop.Final.Trace.Workers.Keccak.RVTheorems
import Slop.Final.Trace.Workers.KeccakSplit.RVTheorems
import Human.Circuits.AddSub.RVTheorems
import Human.Circuits.Bigint.RVTheorems
import Human.Circuits.Blake2G.Theorems
import Human.Circuits.InitsTeardowns.Theorems
import Human.Circuits.JumpBranchSlt.RVTheorems
import Human.Helpers.Context.PCState.Theorems
import Human.ISA.Sail.Theorems
import Human.Trace.Delegation.RVTheorems
import Human.Trace.Families.AddSub.RVTheorems
import Human.Trace.Families.JumpBranchSlt.RVTheorems
import Human.Trace.Families.MulDiv.RVTheorems
import Human.Trace.Families.ShiftBinop.RVTheorems
import Human.Trace.Families.SubwordMemory.RVTheorems
import Human.Trace.ZeroTimestamp
import Human.Trace.WritesRangeChecked
import Human.Trace.TeardownBounds
import Human.Trace.Workers.Bigint.RVTheorems
import Human.Trace.Workers.Blake2G.RVTheorems
import Human.Trace.Workers.Blake2Round.RVTheorems
import Human.Trace.Workers.Keccak.RVTheorems
import Human.Trace.Workers.KeccakSplit.RVTheorems
-- callers1: RV delegation caller claims
import Slop.Final.Circuits.AddSub.RVCallerTheorems
import Slop.Final.Trace.Delegation.RVCallerTheorems
import Human.Circuits.AddSub.RVCallerTheorems
import Human.Trace.Delegation.RVCallerTheorems
import Slop.Final.Trace.UnifiedReduced.RVCallerTheorems
import Human.Trace.UnifiedReduced.RVCallerTheorems
-- P3.1: each imported artifact is the meaning of its transcription
import Slop.Final.Circuits.AddSub.Artifact
import Slop.Final.Circuits.Bigint.Artifact
import Slop.Final.Circuits.Blake2G.Artifact
import Slop.Final.Circuits.Blake2Round.Artifact
import Slop.Final.Circuits.InitsTeardowns.Artifact
import Slop.Final.Circuits.InitsTeardowns.UnifiedArtifact
import Slop.Final.Circuits.JumpBranchSlt.Artifact
import Slop.Final.Circuits.Keccak.Artifact
import Slop.Final.Circuits.KeccakSplit.Chi5.Artifact
import Slop.Final.Circuits.KeccakSplit.ColumnParity.Artifact
import Slop.Final.Circuits.KeccakSplit.ThetaRho.Artifact
import Slop.Final.Circuits.MulDiv.Artifact
import Slop.Final.Circuits.ShiftBinop.Artifact
import Slop.Final.Circuits.SubwordMemory.Artifact
import Slop.Final.Circuits.UnifiedReduced.Artifact
import Slop.Final.Circuits.WordMemory.Artifact
import Slop.Final.Import.Columns
import Slop.Final.Import.Theorems
import Human.Import.Theorems
-- P4.2 non-vacuity: the claims' assumptions can be met
import Slop.Final.Trace.Satisfiable.Pools
import Slop.Final.Trace.Satisfiable.Pooled
import Slop.Final.Trace.Satisfiable.Families
import Slop.Final.Trace.Satisfiable.Unified
import Slop.Final.Trace.Satisfiable.Blake2G
import Slop.Final.Trace.Satisfiable.Keccak
import Slop.Final.Trace.Satisfiable.KeccakSplit
import Slop.Final.Trace.Satisfiable.Blake2Round
import Slop.Final.Trace.Satisfiable.UnifiedCallers
import Slop.Final.Trace.Satisfiable.UnifiedPreparedCallers
import Slop.Final.Trace.Satisfiable.Callers

example : Airbender.AddSub.RVSoundnessClaim := @Airbender.AddSub.rv_soundness
example : Airbender.Bigint.Memory.RVAddressesSoundnessClaim := @Airbender.Bigint.Memory.rv_addresses_soundness
example : Airbender.Blake2G.SoundnessClaim := @Airbender.Blake2G.soundness
example : Airbender.JumpBranchSlt.Comparison.RVSoundnessClaim := @Airbender.JumpBranchSlt.Comparison.rv_soundness
example : Airbender.JumpBranchSlt.Branch.RVSoundnessClaim := @Airbender.JumpBranchSlt.Branch.rv_soundness
example : Airbender.JumpBranchSlt.Jump.RVSoundnessClaim := @Airbender.JumpBranchSlt.Jump.rv_soundness
example : Airbender.MulDiv.RVSoundnessClaim := @Airbender.MulDiv.rv_soundness
example : Airbender.ShiftBinop.RVSoundnessClaim := @Airbender.ShiftBinop.rv_soundness
example : Airbender.SubwordMemory.RVSoundnessClaim := @Airbender.SubwordMemory.rv_soundness
example : Airbender.WordMemory.RVSoundnessClaim := @Airbender.WordMemory.rv_soundness
example : Airbender.PCState.OutgoingBoundsClaim := @Airbender.PCState.outgoing_bounds
example : Airbender.DecodeIsSailClaim := @Airbender.decode_is_sail
example : Airbender.StepIsAirbenderClaim := @Airbender.step_is_airbender
example : Airbender.MachineChecksClaim := @Airbender.machine_checks_claim
example : RV.CallsRun := @RV.calls_run
example : RV.BlakeCompressRun := @RV.blake_compress_run
example : RV.BlakeHashRun := @RV.blake_hash_run
example : RV.BlakeCompressRun10 := @RV.blake_compress_run10
example : RV.BlakeHashRun10 := @RV.blake_hash_run10
example : RV.BlakeGRun := @RV.blake_g_run
example : RV.BlakeGRun10 := @RV.blake_g_run10
example : RV.KeccakSpecial5Run := @RV.keccak_special5_run
example : RV.KeccakF1600Run := @RV.keccak_f1600_run
example : RV.StandardVectors := @RV.standard_vectors
example : Airbender.Delegation.RVNativeMemoryExecutionClaim := @Airbender.Delegation.rv_native_memory_execution
example : Airbender.Delegation.RVOperationMemorySoundnessClaim := @Airbender.Delegation.rv_operation_memory_soundness
example : Airbender.Delegation.RVMemorySoundnessClaim := @Airbender.Delegation.rv_memory_soundness
example : Airbender.Trace.RVAirbenderSoundnessClaim := @Airbender.Trace.rv_airbender_soundness
example : Airbender.Trace.RVNativeBootSoundnessClaim := @Airbender.Trace.rv_native_boot_soundness
example : Airbender.JumpBranchSlt.RVTraceSoundnessClaim := @Airbender.JumpBranchSlt.rv_trace_soundness
example : Airbender.MulDiv.RVTraceSoundnessClaim := @Airbender.MulDiv.rv_trace_soundness
example : Airbender.ShiftBinop.RVTraceSoundnessClaim := @Airbender.ShiftBinop.rv_trace_soundness
example : Airbender.SubwordMemory.RVRamTraceSoundnessClaim := @Airbender.SubwordMemory.rv_ram_trace_soundness
example : Airbender.Trace.RVPooledNativeSoundnessClaim := @Airbender.Trace.rv_pooled_native_soundness
example : Airbender.Trace.BootRamZeroClaim := @Airbender.Trace.boot_ram_zero
example : Airbender.Trace.NonDeterminism.Pooled.RVNativeSoundnessClaim := @Airbender.Trace.NonDeterminism.Pooled.rv_native_soundness
example : Airbender.InitsTeardowns.StandaloneClaim := @Airbender.InitsTeardowns.standalone_claim
example : Airbender.InitsTeardowns.UnifiedClaim := @Airbender.InitsTeardowns.unified_claim
example : Airbender.Trace.NoZeroTimestampWritesClaim := @Airbender.Trace.no_zero_timestamp_writes
example : Airbender.UnifiedReduced.NoZeroTimestampWritesClaim := @Airbender.UnifiedReduced.no_zero_timestamp_writes
example : Airbender.Delegation.NoZeroTimestampWritesClaim := @Airbender.Delegation.no_zero_timestamp_writes
example : Airbender.Keccak.Split.Native.NoZeroTimestampWritesClaim := @Airbender.Keccak.Split.Native.no_zero_timestamp_writes
example : Airbender.Trace.WritesRangeCheckedClaim := @Airbender.Trace.writes_range_checked
example : Airbender.UnifiedReduced.WritesRangeCheckedClaim := @Airbender.UnifiedReduced.writes_range_checked
example : Airbender.Delegation.WritesRangeCheckedClaim := @Airbender.Delegation.writes_range_checked
example : Airbender.Keccak.Split.Native.WritesRangeCheckedClaim := @Airbender.Keccak.Split.Native.writes_range_checked
example : Airbender.InitsTeardowns.WritesRangeCheckedClaim := @Airbender.InitsTeardowns.writes_range_checked
example : Airbender.Trace.TeardownsBoundedClaim := @Airbender.Trace.teardowns_bounded
example : Airbender.UnifiedReduced.TeardownsBoundedClaim := @Airbender.UnifiedReduced.teardowns_bounded
example : Airbender.UnifiedReduced.RVExecutionSoundnessClaim := @Airbender.UnifiedReduced.rv_execution_soundness
example : Airbender.UnifiedReduced.BootRamZeroClaim := @Airbender.UnifiedReduced.boot_ram_zero
example : Airbender.Bigint.Native.RVOperationExecutionClaim := @Airbender.Bigint.Native.rv_operation_execution
example : Airbender.Blake2G.Native.RVWorkvectorSoundnessClaim := @Airbender.Blake2G.Native.rv_workvector_soundness
example : Airbender.Blake2G.Native.RVWorkvectorBoundarySoundnessClaim := @Airbender.Blake2G.Native.rv_workvector_boundary_soundness
example : Airbender.Blake2G.Native.RVWindowSoundnessClaim := @Airbender.Blake2G.Native.rv_window_soundness
example : Airbender.Blake2G.Native.RVOperationExecutionClaim := @Airbender.Blake2G.Native.rv_operation_execution
example : Airbender.Blake2Round.Native.RVOperationExecutionClaim := @Airbender.Blake2Round.Native.rv_operation_execution
example : Airbender.Blake2Round.Native.RVCompressionSoundnessClaim := @Airbender.Blake2Round.Native.rv_compression_soundness
example : Airbender.Blake2Round.Native.RVCompressionBoundarySoundnessClaim := @Airbender.Blake2Round.Native.rv_compression_boundary_soundness
example : Airbender.Blake2Round.Native.RVWindowSoundnessClaim := @Airbender.Blake2Round.Native.rv_window_soundness
example : Airbender.Keccak.Native.RVPermutationBoundarySoundnessClaim := @Airbender.Keccak.Native.rv_permutation_boundary_soundness
example : Airbender.Keccak.Native.RVPermutationSoundnessClaim := @Airbender.Keccak.Native.rv_permutation_soundness
example : Airbender.Keccak.Native.RVOperationExecutionClaim := @Airbender.Keccak.Native.rv_operation_execution
example : Airbender.Keccak.Native.RVWindowSoundnessClaim := @Airbender.Keccak.Native.rv_window_soundness
example : Airbender.Keccak.Split.Native.RVOperationExecutionClaim := @Airbender.Keccak.Split.Native.rv_operation_execution
example : Airbender.Keccak.Split.Native.RVPermutationSoundnessClaim := @Airbender.Keccak.Split.Native.rv_permutation_soundness
-- callers1: RV delegation caller claims
example : Airbender.Delegation.Caller.RVSoundnessClaim := @Airbender.Delegation.Caller.rv_soundness
example : Airbender.Delegation.Caller.RVPcSoundnessClaim := @Airbender.Delegation.Caller.rv_pc_soundness
example : Airbender.Delegation.Caller.RVRequestsSoundnessClaim := @Airbender.Delegation.Caller.rv_requests_soundness
example : Airbender.Delegation.Caller.RVRequestMemorySoundnessClaim := @Airbender.Delegation.Caller.rv_request_memory_soundness
example : Airbender.Delegation.Caller.RVOperationSoundnessClaim := @Airbender.Delegation.Caller.rv_operation_soundness
example : Airbender.Delegation.Caller.RVSharedMemorySoundnessClaim := @Airbender.Delegation.Caller.rv_shared_memory_soundness
example : Airbender.Delegation.Caller.RVSharedOperationSoundnessClaim := @Airbender.Delegation.Caller.rv_shared_operation_soundness
example : Airbender.Delegation.Caller.RVSharedSpanSoundnessClaim := @Airbender.Delegation.Caller.rv_shared_span_soundness
example : Airbender.Delegation.Caller.RVMixedMemorySoundnessClaim := @Airbender.Delegation.Caller.rv_mixed_memory_soundness
example : Airbender.Delegation.Caller.RVWorkerScheduleSoundnessClaim := @Airbender.Delegation.Caller.rv_worker_schedule_soundness
example : Airbender.Delegation.Caller.RVRequestWindowSoundnessClaim := @Airbender.Delegation.Caller.rv_request_window_soundness
example : Airbender.Delegation.Caller.RVRequestHashWindowSoundnessClaim := @Airbender.Delegation.Caller.rv_request_hash_window_soundness
example : Airbender.UnifiedReduced.Caller.RVRequestWindowSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_request_window_soundness
example : Airbender.UnifiedReduced.Caller.RVMixedMemorySoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_mixed_memory_soundness
example : Airbender.UnifiedReduced.Caller.RVSharedSpanSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_shared_span_soundness
example : Airbender.UnifiedReduced.Caller.RVRequestHashWindowSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_request_hash_window_soundness
example : Airbender.UnifiedReduced.Caller.RVMixedWindowSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_mixed_window_soundness
example : Airbender.UnifiedReduced.Caller.RVWindowProjectionSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_window_projection_soundness
example : Airbender.UnifiedReduced.Caller.RVMixedWindowSequenceSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_mixed_window_sequence_soundness
example : Airbender.UnifiedReduced.Caller.RVJointHashWindowSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_joint_hash_window_soundness
example : Airbender.UnifiedReduced.Caller.RVWindowScheduleSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_window_schedule_soundness
example : Airbender.UnifiedReduced.Caller.RVMixedWindowProjectionSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_mixed_window_projection_soundness
example : Airbender.UnifiedReduced.Caller.RVControlPreparationSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_control_preparation_soundness
example : Airbender.UnifiedReduced.Caller.RVControlPreparationWindowSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_control_preparation_window_soundness
example : Airbender.UnifiedReduced.Caller.RVProgramWindowScheduleSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_program_window_schedule_soundness
example : Airbender.UnifiedReduced.Caller.RVPreparedHashWindowSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_prepared_hash_window_soundness
example : Airbender.UnifiedReduced.Caller.RVPreparedHashSequenceSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_prepared_hash_sequence_soundness
example : Airbender.UnifiedReduced.Caller.RVPreparedRoundRegionMasksSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_prepared_round_region_masks_soundness
example : Airbender.UnifiedReduced.Caller.RVPreparedProtocolSequenceSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_prepared_protocol_sequence_soundness
example : Airbender.UnifiedReduced.Caller.RVPreparedRoundMasksSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_prepared_round_masks_soundness
example : Airbender.UnifiedReduced.Caller.RVPreparedRoundWindowSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_prepared_round_window_soundness
example : Airbender.UnifiedReduced.Caller.RVProgramPreparedProtocolSequenceSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_program_prepared_protocol_sequence_soundness
example : Airbender.UnifiedReduced.Caller.RVCallerCyclesSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_caller_cycles_soundness
example : Airbender.UnifiedReduced.Caller.RVPreparedRoundCyclesSoundnessClaim := @Airbender.UnifiedReduced.Caller.rv_prepared_round_cycles_soundness
example : Airbender.AddSub.ArtifactImportClaim := @Airbender.AddSub.artifact_import
example : Airbender.Bigint.ArtifactImportClaim := @Airbender.Bigint.artifact_import
example : Airbender.Blake2G.ArtifactImportClaim := @Airbender.Blake2G.artifact_import
example : Airbender.Blake2Round.ArtifactImportClaim := @Airbender.Blake2Round.artifact_import
example : Airbender.InitsTeardowns.StandaloneImportClaim := @Airbender.InitsTeardowns.standalone_import
example : Airbender.InitsTeardowns.StandaloneBytesClaim := @Airbender.InitsTeardowns.standalone_bytes
example : Airbender.InitsTeardowns.UnifiedImportClaim := @Airbender.InitsTeardowns.unified_import
example : Airbender.JumpBranchSlt.ArtifactImportClaim := @Airbender.JumpBranchSlt.artifact_import
example : Airbender.Keccak.ArtifactImportClaim := @Airbender.Keccak.artifact_import
example : Airbender.Keccak.Split.Chi5.ArtifactImportClaim := @Airbender.Keccak.Split.Chi5.artifact_import
example : Airbender.Keccak.Split.ColumnParity.ArtifactImportClaim := @Airbender.Keccak.Split.ColumnParity.artifact_import
example : Airbender.Keccak.Split.ThetaRho.ArtifactImportClaim := @Airbender.Keccak.Split.ThetaRho.artifact_import
example : Airbender.MulDiv.ArtifactImportClaim := @Airbender.MulDiv.artifact_import
example : Airbender.ShiftBinop.ArtifactImportClaim := @Airbender.ShiftBinop.artifact_import
example : Airbender.SubwordMemory.ArtifactImportClaim := @Airbender.SubwordMemory.artifact_import
example : Airbender.UnifiedReduced.ArtifactImportClaim := @Airbender.UnifiedReduced.artifact_import
example : Airbender.WordMemory.ArtifactImportClaim := @Airbender.WordMemory.artifact_import
example : Airbender.PlacementsClaim := @Airbender.placements_claim
example : Airbender.Json.ParseSoundClaim := @Airbender.Json.parse_sound
example : Airbender.Json.TextUniqueClaim := @Airbender.Json.text_unique
example : Airbender.DecodeClaim := @Airbender.decode_claim
example : Airbender.ConstantsClaim := @Airbender.constants_claim

#print axioms Airbender.AddSub.rv_soundness
#print axioms Airbender.Bigint.Memory.rv_addresses_soundness
#print axioms Airbender.Blake2G.soundness
#print axioms Airbender.JumpBranchSlt.Comparison.rv_soundness
#print axioms Airbender.JumpBranchSlt.Branch.rv_soundness
#print axioms Airbender.JumpBranchSlt.Jump.rv_soundness
#print axioms Airbender.MulDiv.rv_soundness
#print axioms Airbender.ShiftBinop.rv_soundness
#print axioms Airbender.SubwordMemory.rv_soundness
#print axioms Airbender.WordMemory.rv_soundness
#print axioms Airbender.PCState.outgoing_bounds
#print axioms Airbender.decode_is_sail
#print axioms Airbender.step_is_airbender
#print axioms Airbender.machine_checks_claim
#print axioms RV.calls_run
#print axioms RV.blake_compress_run
#print axioms RV.blake_hash_run
#print axioms RV.blake_compress_run10
#print axioms RV.blake_hash_run10
#print axioms RV.blake_g_run
#print axioms RV.blake_g_run10
#print axioms RV.keccak_special5_run
#print axioms RV.keccak_f1600_run
#print axioms RV.standard_vectors
#print axioms Airbender.Delegation.rv_native_memory_execution
#print axioms Airbender.Delegation.rv_operation_memory_soundness
#print axioms Airbender.Delegation.rv_memory_soundness
#print axioms Airbender.Trace.rv_airbender_soundness
#print axioms Airbender.Trace.rv_native_boot_soundness
#print axioms Airbender.JumpBranchSlt.rv_trace_soundness
#print axioms Airbender.MulDiv.rv_trace_soundness
#print axioms Airbender.ShiftBinop.rv_trace_soundness
#print axioms Airbender.SubwordMemory.rv_ram_trace_soundness
#print axioms Airbender.Trace.rv_pooled_native_soundness
#print axioms Airbender.Trace.boot_ram_zero
#print axioms Airbender.Trace.NonDeterminism.Pooled.rv_native_soundness
#print axioms Airbender.InitsTeardowns.standalone_claim
#print axioms Airbender.InitsTeardowns.unified_claim
#print axioms Airbender.Trace.no_zero_timestamp_writes
#print axioms Airbender.UnifiedReduced.no_zero_timestamp_writes
#print axioms Airbender.Delegation.no_zero_timestamp_writes
#print axioms Airbender.Keccak.Split.Native.no_zero_timestamp_writes
#print axioms Airbender.Trace.writes_range_checked
#print axioms Airbender.UnifiedReduced.writes_range_checked
#print axioms Airbender.Delegation.writes_range_checked
#print axioms Airbender.Keccak.Split.Native.writes_range_checked
#print axioms Airbender.InitsTeardowns.writes_range_checked
#print axioms Airbender.Trace.teardowns_bounded
#print axioms Airbender.UnifiedReduced.teardowns_bounded
#print axioms Airbender.UnifiedReduced.rv_execution_soundness
#print axioms Airbender.UnifiedReduced.boot_ram_zero
#print axioms Airbender.Bigint.Native.rv_operation_execution
#print axioms Airbender.Blake2G.Native.rv_workvector_soundness
#print axioms Airbender.Blake2G.Native.rv_workvector_boundary_soundness
#print axioms Airbender.Blake2G.Native.rv_window_soundness
#print axioms Airbender.Blake2G.Native.rv_operation_execution
#print axioms Airbender.Blake2Round.Native.rv_operation_execution
#print axioms Airbender.Blake2Round.Native.rv_compression_soundness
#print axioms Airbender.Blake2Round.Native.rv_compression_boundary_soundness
#print axioms Airbender.Blake2Round.Native.rv_window_soundness
#print axioms Airbender.Keccak.Native.rv_permutation_boundary_soundness
#print axioms Airbender.Keccak.Native.rv_permutation_soundness
#print axioms Airbender.Keccak.Native.rv_operation_execution
#print axioms Airbender.Keccak.Native.rv_window_soundness
#print axioms Airbender.Keccak.Split.Native.rv_operation_execution
#print axioms Airbender.Keccak.Split.Native.rv_permutation_soundness
-- callers1: RV delegation caller claims
#print axioms Airbender.Delegation.Caller.rv_soundness
#print axioms Airbender.Delegation.Caller.rv_pc_soundness
#print axioms Airbender.Delegation.Caller.rv_requests_soundness
#print axioms Airbender.Delegation.Caller.rv_request_memory_soundness
#print axioms Airbender.Delegation.Caller.rv_operation_soundness
#print axioms Airbender.Delegation.Caller.rv_shared_memory_soundness
#print axioms Airbender.Delegation.Caller.rv_shared_operation_soundness
#print axioms Airbender.Delegation.Caller.rv_shared_span_soundness
#print axioms Airbender.Delegation.Caller.rv_mixed_memory_soundness
#print axioms Airbender.Delegation.Caller.rv_worker_schedule_soundness
#print axioms Airbender.Delegation.Caller.rv_request_window_soundness
#print axioms Airbender.Delegation.Caller.rv_request_hash_window_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_request_window_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_mixed_memory_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_shared_span_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_request_hash_window_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_mixed_window_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_window_projection_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_mixed_window_sequence_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_joint_hash_window_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_window_schedule_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_mixed_window_projection_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_control_preparation_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_control_preparation_window_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_program_window_schedule_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_prepared_hash_window_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_prepared_hash_sequence_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_prepared_round_region_masks_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_prepared_protocol_sequence_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_prepared_round_masks_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_prepared_round_window_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_program_prepared_protocol_sequence_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_caller_cycles_soundness
#print axioms Airbender.UnifiedReduced.Caller.rv_prepared_round_cycles_soundness
#print axioms Airbender.AddSub.artifact_import
#print axioms Airbender.Bigint.artifact_import
#print axioms Airbender.Blake2G.artifact_import
#print axioms Airbender.Blake2Round.artifact_import
#print axioms Airbender.InitsTeardowns.standalone_import
#print axioms Airbender.InitsTeardowns.standalone_bytes
#print axioms Airbender.InitsTeardowns.unified_import
#print axioms Airbender.JumpBranchSlt.artifact_import
#print axioms Airbender.Keccak.artifact_import
#print axioms Airbender.Keccak.Split.Chi5.artifact_import
#print axioms Airbender.Keccak.Split.ColumnParity.artifact_import
#print axioms Airbender.Keccak.Split.ThetaRho.artifact_import
#print axioms Airbender.MulDiv.artifact_import
#print axioms Airbender.ShiftBinop.artifact_import
#print axioms Airbender.SubwordMemory.artifact_import
#print axioms Airbender.UnifiedReduced.artifact_import
#print axioms Airbender.WordMemory.artifact_import
#print axioms Airbender.placements_claim
#print axioms Airbender.Json.parse_sound
#print axioms Airbender.Json.text_unique
#print axioms Airbender.decode_claim
#print axioms Airbender.constants_claim
-- P4.2 non-vacuity (statements)
example : Airbender.Delegation.RVNativeMemoryExecutionSatisfiableClaim := @Airbender.Delegation.rv_native_memory_execution_satisfiable
#print axioms Airbender.Delegation.rv_native_memory_execution_satisfiable
example : Airbender.Delegation.RVOperationMemorySoundnessSatisfiableClaim := @Airbender.Delegation.rv_operation_memory_soundness_satisfiable
#print axioms Airbender.Delegation.rv_operation_memory_soundness_satisfiable
example : Airbender.Delegation.RVMemorySoundnessSatisfiableClaim := @Airbender.Delegation.rv_memory_soundness_satisfiable
#print axioms Airbender.Delegation.rv_memory_soundness_satisfiable
example : Airbender.Delegation.NoZeroTimestampWritesSatisfiableClaim := @Airbender.Delegation.no_zero_timestamp_writes_satisfiable
#print axioms Airbender.Delegation.no_zero_timestamp_writes_satisfiable
example : Airbender.Keccak.Split.Native.NoZeroTimestampWritesSatisfiableClaim := @Airbender.Keccak.Split.Native.no_zero_timestamp_writes_satisfiable
#print axioms Airbender.Keccak.Split.Native.no_zero_timestamp_writes_satisfiable
example : Airbender.Delegation.WritesRangeCheckedSatisfiableClaim := @Airbender.Delegation.writes_range_checked_satisfiable
#print axioms Airbender.Delegation.writes_range_checked_satisfiable
example : Airbender.InitsTeardowns.WritesRangeCheckedSatisfiableClaim := @Airbender.InitsTeardowns.writes_range_checked_satisfiable
#print axioms Airbender.InitsTeardowns.writes_range_checked_satisfiable
example : Airbender.Bigint.Native.RVOperationExecutionSatisfiableClaim := @Airbender.Bigint.Native.rv_operation_execution_satisfiable
#print axioms Airbender.Bigint.Native.rv_operation_execution_satisfiable
example : Airbender.Trace.RVPooledNativeSoundnessSatisfiableClaim := @Airbender.Trace.rv_pooled_native_soundness_satisfiable
#print axioms Airbender.Trace.rv_pooled_native_soundness_satisfiable
example : Airbender.Trace.BootRamZeroSatisfiableClaim := @Airbender.Trace.boot_ram_zero_satisfiable
#print axioms Airbender.Trace.boot_ram_zero_satisfiable
example : Airbender.Trace.NonDeterminism.Pooled.RVNativeSoundnessSatisfiableClaim := @Airbender.Trace.NonDeterminism.Pooled.rv_native_soundness_satisfiable
#print axioms Airbender.Trace.NonDeterminism.Pooled.rv_native_soundness_satisfiable
example : Airbender.Trace.NoZeroTimestampWritesSatisfiableClaim := @Airbender.Trace.no_zero_timestamp_writes_satisfiable
#print axioms Airbender.Trace.no_zero_timestamp_writes_satisfiable
example : Airbender.Trace.WritesRangeCheckedSatisfiableClaim := @Airbender.Trace.writes_range_checked_satisfiable
#print axioms Airbender.Trace.writes_range_checked_satisfiable
example : Airbender.Trace.TeardownsBoundedSatisfiableClaim := @Airbender.Trace.teardowns_bounded_satisfiable
#print axioms Airbender.Trace.teardowns_bounded_satisfiable
example : Airbender.Trace.RVAirbenderSoundnessSatisfiableClaim := @Airbender.Trace.rv_airbender_soundness_satisfiable
#print axioms Airbender.Trace.rv_airbender_soundness_satisfiable
example : Airbender.Trace.RVNativeBootSoundnessSatisfiableClaim := @Airbender.Trace.rv_native_boot_soundness_satisfiable
#print axioms Airbender.Trace.rv_native_boot_soundness_satisfiable
example : Airbender.UnifiedReduced.RVExecutionSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.rv_execution_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.rv_execution_soundness_satisfiable
example : Airbender.UnifiedReduced.BootRamZeroSatisfiableClaim := @Airbender.UnifiedReduced.boot_ram_zero_satisfiable
#print axioms Airbender.UnifiedReduced.boot_ram_zero_satisfiable
example : Airbender.UnifiedReduced.NoZeroTimestampWritesSatisfiableClaim := @Airbender.UnifiedReduced.no_zero_timestamp_writes_satisfiable
#print axioms Airbender.UnifiedReduced.no_zero_timestamp_writes_satisfiable
example : Airbender.UnifiedReduced.WritesRangeCheckedSatisfiableClaim := @Airbender.UnifiedReduced.writes_range_checked_satisfiable
#print axioms Airbender.UnifiedReduced.writes_range_checked_satisfiable
example : Airbender.UnifiedReduced.TeardownsBoundedSatisfiableClaim := @Airbender.UnifiedReduced.teardowns_bounded_satisfiable
#print axioms Airbender.UnifiedReduced.teardowns_bounded_satisfiable
example : Airbender.Blake2G.Native.RVOperationExecutionSatisfiableClaim := @Airbender.Blake2G.Native.rv_operation_execution_satisfiable
#print axioms Airbender.Blake2G.Native.rv_operation_execution_satisfiable
example : Airbender.Keccak.Native.RVOperationExecutionSatisfiableClaim := @Airbender.Keccak.Native.rv_operation_execution_satisfiable
#print axioms Airbender.Keccak.Native.rv_operation_execution_satisfiable
example : Airbender.Keccak.Split.Native.RVOperationExecutionSatisfiableClaim := @Airbender.Keccak.Split.Native.rv_operation_execution_satisfiable
#print axioms Airbender.Keccak.Split.Native.rv_operation_execution_satisfiable
example : Airbender.Keccak.Split.Native.WritesRangeCheckedSatisfiableClaim := @Airbender.Keccak.Split.Native.writes_range_checked_satisfiable
#print axioms Airbender.Keccak.Split.Native.writes_range_checked_satisfiable
example : Airbender.Blake2Round.Native.RVOperationExecutionSatisfiableClaim := @Airbender.Blake2Round.Native.rv_operation_execution_satisfiable
#print axioms Airbender.Blake2Round.Native.rv_operation_execution_satisfiable
example : Airbender.UnifiedReduced.Caller.RVMixedMemorySoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_mixed_memory_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_mixed_memory_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVRequestWindowSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_request_window_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_request_window_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVMixedWindowSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_mixed_window_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_mixed_window_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVWindowProjectionSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_window_projection_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_window_projection_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVWindowScheduleSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_window_schedule_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_window_schedule_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVMixedWindowProjectionSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_mixed_window_projection_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_mixed_window_projection_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVMixedWindowSequenceSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_mixed_window_sequence_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_mixed_window_sequence_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVCallerCyclesSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_caller_cycles_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_caller_cycles_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVControlPreparationSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_control_preparation_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_control_preparation_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVControlPreparationWindowSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_control_preparation_window_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_control_preparation_window_soundness_satisfiable

example : Airbender.JumpBranchSlt.RVTraceSoundnessSatisfiableClaim := @Airbender.JumpBranchSlt.rv_trace_soundness_satisfiable
#print axioms Airbender.JumpBranchSlt.rv_trace_soundness_satisfiable
example : Airbender.MulDiv.RVTraceSoundnessSatisfiableClaim := @Airbender.MulDiv.rv_trace_soundness_satisfiable
#print axioms Airbender.MulDiv.rv_trace_soundness_satisfiable
example : Airbender.ShiftBinop.RVTraceSoundnessSatisfiableClaim := @Airbender.ShiftBinop.rv_trace_soundness_satisfiable
#print axioms Airbender.ShiftBinop.rv_trace_soundness_satisfiable
example : Airbender.SubwordMemory.RVRamTraceSoundnessSatisfiableClaim := @Airbender.SubwordMemory.rv_ram_trace_soundness_satisfiable
#print axioms Airbender.SubwordMemory.rv_ram_trace_soundness_satisfiable

example : Airbender.Delegation.Caller.RVSoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_soundness_satisfiable
example : Airbender.Delegation.Caller.RVPcSoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_pc_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_pc_soundness_satisfiable
example : Airbender.Delegation.Caller.RVRequestsSoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_requests_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_requests_soundness_satisfiable
example : Airbender.Delegation.Caller.RVRequestMemorySoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_request_memory_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_request_memory_soundness_satisfiable
example : Airbender.Delegation.Caller.RVOperationSoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_operation_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_operation_soundness_satisfiable
example : Airbender.Delegation.Caller.RVSharedMemorySoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_shared_memory_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_shared_memory_soundness_satisfiable
example : Airbender.Delegation.Caller.RVSharedOperationSoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_shared_operation_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_shared_operation_soundness_satisfiable
example : Airbender.Delegation.Caller.RVMixedMemorySoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_mixed_memory_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_mixed_memory_soundness_satisfiable
example : Airbender.Delegation.Caller.RVWorkerScheduleSoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_worker_schedule_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_worker_schedule_soundness_satisfiable
example : Airbender.Delegation.Caller.RVRequestWindowSoundnessSatisfiableClaim := @Airbender.Delegation.Caller.rv_request_window_soundness_satisfiable
#print axioms Airbender.Delegation.Caller.rv_request_window_soundness_satisfiable
example : Airbender.UnifiedReduced.Caller.RVProgramWindowScheduleSoundnessSatisfiableClaim := @Airbender.UnifiedReduced.Caller.rv_program_window_schedule_soundness_satisfiable
#print axioms Airbender.UnifiedReduced.Caller.rv_program_window_schedule_soundness_satisfiable
example : Airbender.Blake2G.Native.RVWorkvectorSoundnessSatisfiableClaim := @Airbender.Blake2G.Native.rv_workvector_soundness_satisfiable
#print axioms Airbender.Blake2G.Native.rv_workvector_soundness_satisfiable
example : Airbender.Blake2G.Native.RVWorkvectorBoundarySoundnessSatisfiableClaim := @Airbender.Blake2G.Native.rv_workvector_boundary_soundness_satisfiable
#print axioms Airbender.Blake2G.Native.rv_workvector_boundary_soundness_satisfiable
example : Airbender.Blake2G.Native.RVWindowSoundnessSatisfiableClaim := @Airbender.Blake2G.Native.rv_window_soundness_satisfiable
#print axioms Airbender.Blake2G.Native.rv_window_soundness_satisfiable
