import Human.ISA.Sail.WholeRun
import Human.Compiler.NativeTargets

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler

/-- Current cached certificates, public boot data and exact matching give a complete Airbender machine run.
    The public lookup tables, input stream and production profile are premises. Worker lookups use the fixed
    public worker tables. The description setup fields are not premises. -/
def UnrolledFullFromNativeSailClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits →
    NoSpecial5 program →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables → NativePublicSetup.CoversROM cells →
    ∀ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers →
      SailRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)


/-- Current cached certificates, public boot data and exact matching give a complete Airbender machine run.
    The public lookup tables, input stream and production profile are premises. Worker lookups use the fixed
    public worker tables. The description setup fields are not premises. -/
def UnrolledReducedFromNativeSailClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables → NativePublicSetup.CoversROM cells →
    ∀ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers →
      SailRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)


/-- Current cached certificates, public boot data and exact matching give a complete Airbender machine run.
    The public lookup tables, input stream and production profile are premises. Worker lookups use the fixed
    public worker tables. The description setup fields are not premises. -/
def UnifiedFromNativeSailClaim : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits →
    NoSpecial5 program → UnifiedStreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables →
    ∀ certificates : List (UnifiedLogicalRowCertificate tables),
      UnifiedNativeArguments tables certificates trace workers →
      SailRealizes trace initial cells (unifiedReadCount trace)


/-- The public data and native certificates of this Sail claim have a simultaneous witness. -/
def UnrolledFullFromNativeSailSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers

/-- The public data and native certificates of this Sail claim have a simultaneous witness. -/
def UnrolledReducedFromNativeSailSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers

/-- The public data and native certificates of this Sail claim have a simultaneous witness. -/
def UnifiedFromNativeSailSatisfiableClaim : Prop :=
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    NoSpecial5 program ∧ UnifiedStreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    ∃ certificates : List (UnifiedLogicalRowCertificate tables),
      UnifiedNativeArguments tables certificates trace workers

end Airbender.Trace.Machine.Native
