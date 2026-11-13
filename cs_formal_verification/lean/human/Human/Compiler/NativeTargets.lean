module
public import Human.Trace.Machine.Model
public import Human.Trace.Machine.Theorems
public import Human.Trace.Machine.ExternalInput
public import Human.Compiler.NativePublicSetup

@[expose] public section

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler


/-- The full unsigned production machine executes the whole accepted trace, including standard and split workers.
    Public premises bind ROM bytes, register seeds, all initialization instances, their checked top bits,
    the typed full statement verifier boundary, and the ROM tables. Worker tables are an explicit setup interface.
    Native physical equations and exact lookup certificates supply CPU constraints and decoder membership.
    Worker constraints and state, request and memory matching remain independent interfaces.
    Response ports bind the independent input stream. Special5 and `mop.r.N` are excluded. Delegation validity is not a premise. -/
def UnrolledFullFromNative : Prop :=
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
      RVRealizes trace initial cells

/-- The reduced production machine executes the whole accepted trace with modular operations and round calls.
    Public premises bind ROM bytes, zero register seeds, all initialization instances, checked top bits,
    the typed full statement verifier boundary and ROM tables. Worker setup is explicit.
    The production program projection restricts the CPU and delegation families.
    Native physical equations and exact lookup certificates supply CPU constraints and decoder membership.
    Worker constraints and state, request and memory matching remain independent interfaces.
    Response ports bind the independent input stream. Delegation validity is not a premise. -/
def UnrolledReducedFromNative : Prop :=
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
      RVRealizes trace initial cells

/-- The unified production machine executes the whole accepted trace with modular and delegation operations.
    Public premises bind ROM bytes, register seeds, all trailing initialization instances and their checked top bits,
    the typed full statement verifier boundary and the unified ROM table. Worker setup is explicit.
    Native physical equations and exact lookup certificates supply CPU constraints and decoder membership.
    Worker constraints and state, request and memory matching remain independent interfaces.
    Response ports bind the independent input stream. Special5 is excluded. Delegation validity is not a premise. The initialized inline windows lie below `2 ^ 31`. -/
def UnifiedFromNative : Prop :=
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
      RVRealizes trace initial cells

end Airbender.Trace.Machine.Native

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler

/-- The exact public boot and native argument premises hold for an empty submitted trace. -/
def UnrolledFullFromNativeSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    trace.rows = [] ∧ workers.standard.rows = [] ∧ workers.split.rows = [] ∧
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits ∧
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) ∧
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NoSpecial5 program ∧ NoMopR program ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers

/-- The exact public boot and native argument premises hold for an empty submitted trace. -/
def UnrolledReducedFromNativeSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    trace.rows = [] ∧ workers.standard.rows = [] ∧ workers.split.rows = [] ∧
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits ∧
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) ∧
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers

/-- The exact public boot and native argument premises hold for an empty submitted trace. -/
def UnifiedFromNativeSatisfiableClaim : Prop :=
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    trace.rows = [] ∧ workers.standard.rows = [] ∧ workers.split.rows = [] ∧
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    trace.rom = UnifiedReduced.Setup.tableRV initial ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NoSpecial5 program ∧ UnifiedStreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    ∃ certificates : List (UnifiedLogicalRowCertificate tables),
      UnifiedNativeArguments tables certificates trace workers

end Airbender.Trace.Machine.Native
