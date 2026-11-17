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
    the typed full statement verifier boundary, and the public CPU lookup tables.
    Native CPU certificates supply the CPU equations, lookups and decoder membership.
    Cached worker certificates supply every worker equation, lookup and participation flag.
    Worker lookups use the fixed public worker tables. The description setup fields `trace.rom` and
    `workers.standard.setup` are not premises.
    State, request and memory matching are explicit interfaces.
    Response ports bind the independent input stream. Special5 and `mop.r.N` are excluded. Delegation validity is not a premise. -/
def UnrolledFullFromNative : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits →
    NoSpecial5 program →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables → NativePublicSetup.CoversROM cells →
    ∀ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers →
      RVRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)

/-- The reduced production machine executes the whole accepted trace with modular operations and round calls.
    Public premises bind ROM bytes, zero register seeds, all initialization instances, checked top bits,
    the typed full statement verifier boundary and the public CPU lookup tables.
    The production program projection restricts the CPU and delegation families.
    Native CPU certificates supply the CPU equations, lookups and decoder membership.
    Cached worker certificates supply every worker equation, lookup and participation flag.
    Worker lookups use the fixed public worker tables. The description setup fields `trace.rom` and
    `workers.standard.setup` are not premises.
    State, request and memory matching are explicit interfaces.
    Response ports bind the independent input stream. Delegation validity is not a premise. -/
def UnrolledReducedFromNative : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables → NativePublicSetup.CoversROM cells →
    ∀ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers →
      RVRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)

/-- The unified production machine executes the whole accepted trace with modular and delegation operations.
    Public premises bind ROM bytes, register seeds, all trailing initialization instances and their checked top bits,
    the typed full statement verifier boundary and the public unified lookup tables.
    Native CPU certificates supply the CPU equations, lookups and decoder membership.
    Cached worker certificates supply every worker equation, lookup and participation flag.
    Worker lookups use the fixed public worker tables. The description setup fields `trace.rom` and
    `workers.standard.setup` are not premises.
    State, request and memory matching are explicit interfaces.
    Response ports bind the independent input stream. Special5 is excluded. Delegation validity is not a premise. The initialized inline windows lie below `2 ^ 31`. -/
def UnifiedFromNative : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits →
    NoSpecial5 program → UnifiedStreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables →
    ∀ certificates : List (UnifiedLogicalRowCertificate tables),
      UnifiedNativeArguments tables certificates trace workers →
      RVRealizes trace initial cells (unifiedReadCount trace)

end Airbender.Trace.Machine.Native

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler

/-- One submitted CPU row meets the exact public boot and native argument premises. -/
def UnrolledFullFromNativeSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    trace.rows.length = 1 ∧ workers.standard.rows = [] ∧ workers.split.rows = [] ∧
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers

/-- One submitted CPU row meets the exact public boot and native argument premises. -/
def UnrolledReducedFromNativeSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    trace.rows.length = 1 ∧ workers.standard.rows = [] ∧ workers.split.rows = [] ∧
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers

/-- A loop trace with sixteen CPU rows and two worker rows meets the exact native target premises. -/
def UnifiedFromNativeSatisfiableClaim : Prop :=
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    trace.rows.length = 16 ∧ workers.standard.rows.length = 2 ∧ workers.split.rows = [] ∧
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    NoSpecial5 program ∧ UnifiedStreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    ∃ certificates : List (UnifiedLogicalRowCertificate tables),
      UnifiedNativeArguments tables certificates trace workers

end Airbender.Trace.Machine.Native
