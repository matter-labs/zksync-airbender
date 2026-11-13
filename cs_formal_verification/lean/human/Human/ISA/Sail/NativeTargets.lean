import Human.ISA.Sail.WholeRun
import Human.Compiler.NativeTargets

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler

/-- Current cached certificates, public boot data and exact matching give a complete Airbender machine run.
    The setup, worker, input-stream and production-profile interfaces are explicit. -/
def UnrolledFullFromNativeSailClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits →
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) →
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NoSpecial5 program → NoMopR program →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables → NativePublicSetup.CoversROM cells →
    ∀ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers →
      SailRealizes trace initial cells


/-- Current cached certificates, public boot data and exact matching give a complete Airbender machine run.
    The setup, worker, input-stream and production-profile interfaces are explicit. -/
def UnrolledReducedFromNativeSailClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits →
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) →
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables → NativePublicSetup.CoversROM cells →
    ∀ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers →
      SailRealizes trace initial cells


/-- Current cached certificates, public boot data and exact matching give a complete Airbender machine run.
    The setup, worker, input-stream and production-profile interfaces are explicit. -/
def UnifiedFromNativeSailClaim : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits →
    trace.rom = UnifiedReduced.Setup.tableRV initial →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NoSpecial5 program → UnifiedStreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables →
    ∀ certificates : List (UnifiedLogicalRowCertificate tables),
      UnifiedNativeArguments tables certificates trace workers →
      SailRealizes trace initial cells


end Airbender.Trace.Machine.Native
