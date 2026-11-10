import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Helpers.Context.PaddingBoundary.Theorems
import Airbender.Proofs.UnifiedReduced.PaddingBoundary
import Airbender.Review.Trace.Families.AddSub.Theorems
import Airbender.Review.Trace.Soundness
import Airbender.Review.Trace.UnifiedReduced.Theorems

namespace Airbender.Trace

/-- Original Sail execution for the whole layout under external masked tuple
    closure. Only execute-one occurrences retire; arbitrary inactive columns
    contribute identities. Public inputs/decoding use that derived projection.
    Native initial/terminal PC and memory boundaries are preserved. -/
theorem padded_sail_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary (PaddingBoundary.active trace) before cells program)
    (loads : NoDiscardedLoads program) (accepted : PaddingBoundary.AcceptedLayout trace)
    (decoded : Decoded (PaddingBoundary.active trace) program) :
    Realizes (SailStep program) trace before cells :=
  sail_soundness (trace := PaddingBoundary.active trace) inputs loads (PaddingBoundary.acceptance_soundness accepted) decoded

/-- Six-family native boot/ROM execution with the same external mask boundary.
    Canonical verifier-PC closure remains explicit in the existing public inputs;
    inactive raw PC transitions are absent from its projected state path. -/
theorem padded_pooled_native_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : PooledTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs (PaddingBoundary.active trace) before cells program)
    (accepted : PaddingBoundary.AcceptedLayout trace)
    (decoded : PooledDecoded (PaddingBoundary.active trace) program) :
    Realizes (PooledStep program) trace before cells (ROMView.token before) :=
  pooled_native_soundness (trace := PaddingBoundary.active trace) inputs (PaddingBoundary.acceptance_soundness accepted) decoded

end Airbender.Trace

namespace Airbender.UnifiedReduced

/-- Original standard/TRIADD/XORROT whole execution from a padded unified layout.
    The contribution boundary derives participation; configuration, code/data
    profiles, modeled tables and existing field/inverse conditions are unchanged. -/
theorem Mixed.padded_execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Mixed.Inputs (PaddingBoundary.active trace) initial cells program)
    (accepted : PaddingBoundary.AcceptedLayout trace)
    (decoded : Decoded (PaddingBoundary.active trace) program) :
    Trace.Realizes (Mixed.Step program) trace initial cells (Trace.ROMView.token initial) :=
  Mixed.execution_soundness hp clockInverse byteInverse (trace := PaddingBoundary.active trace) inputs (PaddingBoundary.acceptance_soundness accepted) decoded

/-- Full masked machine/worker/state/request closure derives the old shared
    architectural acceptance contract, including full-CSR request multiplicity. -/
theorem Caller.Padding.acceptance_soundness [Fact p.Prime]
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (accepted : Caller.Padding.AcceptedLayout data program) :
    Caller.MixedMemoryAccepted (Caller.Padding.active data) program :=
  Caller.Padding.Proofs.projected_acceptance accepted

/-- One shared selected execution follows from the whole masked layout.
    Execute-one zero-clock workers and invalid bigint controls remain admitted;
    this is the existing caller observation certificate, not full custom-CSR
    reference execution. Worker ROM and all previous public scopes stay explicit. -/
theorem Caller.padded_mixed_cycle_soundness
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.Padding.AcceptedLayout data program)
    (inputs : Caller.MixedMemoryInputs (Caller.Padding.active data) program initial ca oa cells)
    (profile : Caller.RetirementProfile (Caller.Padding.active data) program initial cells) :
    Caller.MixedCycleEffects (Caller.Padding.active data) program initial cells :=
  Caller.mixed_cycle_soundness (Caller.Padding.acceptance_soundness accepted) inputs profile

end Airbender.UnifiedReduced
