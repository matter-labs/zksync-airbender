module
public import Human.Compiler.NativeTargets
public import Human.Compiler.MemoryComposition
public import Human.Compiler.CertificateMemory

@[expose] public section
namespace Airbender.Compiler.NativeMemory
open Trace Trace.Machine

/-- The single native RAM permutation of a padded layout. The execute column of each CPU and worker row masks all of
    its tokens, so a padding row contributes only identity factors. -/
def PaddedRamPermutation {Kind : Type} [CircuitLayout Kind] (trace : Data babyBearModulus Kind)
    (workers : WorkerPools babyBearModulus) : Prop :=
  (some (stateToken trace.initial) :: trace.initialMemory.map some ++
      PaddingBoundary.contributions trace.rows (fun row => row.assignment row.columns.execute) cpuWrites ++
      PaddingBoundary.contributions workers.standard.rows (fun row => row.assignment row.columns.execute)
        standardWrites ++
      PaddingBoundary.contributions workers.split.rows (fun row => row.assignment row.columns.execute)
        splitWrites).Perm
    (some (stateToken trace.terminal) :: trace.terminalMemory.map some ++
      PaddingBoundary.contributions trace.rows (fun row => row.assignment row.columns.execute) cpuReads ++
      PaddingBoundary.contributions workers.standard.rows (fun row => row.assignment row.columns.execute)
        standardReads ++
      PaddingBoundary.contributions workers.split.rows (fun row => row.assignment row.columns.execute)
        splitReads)

end Airbender.Compiler.NativeMemory

namespace Airbender.Compiler
open Airbender.Trace

/-- Cached CPU and worker certificates, their extension values under shared challenges and the single native RAM
    permutation of the production prover. -/
structure UnrolledPermutationArguments {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (tables : ProgramLookupRows) (certificates : List (ProgramLogicalRowCertificate tables)) (values : List (GKRAddress → E))
    (trace : PooledTrace babyBearModulus) (workers : Machine.WorkerPools babyBearModulus) : Prop
    where
  /-- Native worker certificates with extension values describe both submitted worker pools exactly, in order. -/
  workerRows : WorkerRowsExtended challenges workers
  /-- Certificates describe exactly the submitted CPU rows, in order. -/
  rows : trace.rows = certificates.map (·.row)
  /-- The extension values of the CPU certificates meet the extension semantics under the same challenges. -/
  extensions : ProgramExtensions challenges (certificates.map (·.toProgramRowCertificate)) values
  /-- The PC-state, request, register and RAM tokens of all rows share one permutation. -/
  production : NativeMemory.RamPermutation trace workers

/-- Cached unified and worker certificates, their extension values under shared challenges and the single native RAM
    permutation of the production prover. -/
structure UnifiedPermutationArguments {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (tables : ProgramLookupRows) (certificates : List (UnifiedLogicalRowCertificate tables)) (values : List (GKRAddress → E))
    (trace : UnifiedTrace babyBearModulus) (workers : Machine.WorkerPools babyBearModulus) : Prop
    where
  /-- Native worker certificates with extension values describe both submitted worker pools exactly, in order. -/
  workerRows : WorkerRowsExtended challenges workers
  /-- Certificates describe exactly the submitted CPU rows, in order. -/
  rows : trace.rows = certificates.map (·.row)
  /-- The extension values of the CPU certificates meet the extension semantics under the same challenges. -/
  extensions : UnifiedExtensions challenges (certificates.map (·.toUnifiedRowCertificate)) values
  /-- The PC-state, request, register and RAM tokens of all rows share one permutation. -/
  production : NativeMemory.RamPermutation trace workers

/-- A padded unrolled layout: certificates for active and padding rows, their extension values under shared
    challenges and the single masked RAM permutation. -/
structure PaddedUnrolledPermutationArguments {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (tables : ProgramLookupRows) (certificates : List (ProgramRowCertificate tables)) (values : List (GKRAddress → E))
    (trace : PooledTrace babyBearModulus) (workers : Machine.WorkerPools babyBearModulus) : Prop
    where
  /-- Native worker certificates with extension values describe both submitted worker pools exactly, in order. -/
  workerRows : PaddedWorkerRowsExtended challenges workers
  /-- Certificates describe exactly the submitted CPU rows, in order. -/
  rows : trace.rows = certificates.map (·.row)
  /-- The extension values of the CPU certificates meet the extension semantics under the same challenges. -/
  extensions : ProgramExtensions challenges (certificates) values
  /-- Each CPU execute selector is Boolean: one marks an active row and zero a padding row. -/
  selectors : ∀ certificate ∈ certificates,
    certificate.row.assignment certificate.row.columns.execute = 0 ∨
      certificate.row.assignment certificate.row.columns.execute = 1
  /-- The PC-state, request, register and RAM tokens of all rows share one permutation. -/
  production : NativeMemory.PaddedRamPermutation trace workers

/-- A padded unified layout: certificates for active and padding rows, their extension values under shared
    challenges and the single masked RAM permutation. -/
structure PaddedUnifiedPermutationArguments {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (tables : ProgramLookupRows) (certificates : List (UnifiedRowCertificate tables)) (values : List (GKRAddress → E))
    (trace : UnifiedTrace babyBearModulus) (workers : Machine.WorkerPools babyBearModulus) : Prop
    where
  /-- Native worker certificates with extension values describe both submitted worker pools exactly, in order. -/
  workerRows : PaddedWorkerRowsExtended challenges workers
  /-- Certificates describe exactly the submitted CPU rows, in order. -/
  rows : trace.rows = certificates.map (·.row)
  /-- The extension values of the CPU certificates meet the extension semantics under the same challenges. -/
  extensions : UnifiedExtensions challenges (certificates) values
  /-- Each CPU execute selector is Boolean: one marks an active row and zero a padding row. -/
  selectors : ∀ certificate ∈ certificates,
    certificate.row.assignment certificate.row.columns.execute = 0 ∨
      certificate.row.assignment certificate.row.columns.execute = 1
  /-- The PC-state, request, register and RAM tokens of all rows share one permutation. -/
  production : NativeMemory.PaddedRamPermutation trace workers

end Airbender.Compiler

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler PaddingBoundary

/-- The premises of `UnrolledFullFromNative`, with the single native RAM permutation of the production prover as the
    only matching premise, give its result. The certificates carry their extension values under shared challenges,
    so each submitted row gives its RAM outputs from the tokens of that permutation. -/
def UnrolledFullFromNativePermutation : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits →
    NoSpecial5 program →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables →
    NativePublicSetup.CoversROM cells →
    ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
      (certificates : List (ProgramLogicalRowCertificate tables)) (values : List (GKRAddress → E)),
      UnrolledPermutationArguments challenges tables certificates values trace workers →
      RVRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)

/-- One submitted CPU row meets the exact public boot premises, its extension values and the single RAM permutation. -/
def UnrolledFullFromNativePermutationSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    NativePublicSetup.CoversROM cells ∧
    ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (certificates : List (ProgramLogicalRowCertificate tables))
      (values : List (GKRAddress → NativeArithmetic.F)),
      UnrolledPermutationArguments challenges tables certificates values trace workers ∧
      trace.rows.length = 1 ∧ workers.standard.rows = [] ∧ workers.split.rows = []

/-- The premises of `UnrolledReducedFromNative`, with the single native RAM permutation of the production prover as
    the only matching premise, give its result. The certificates carry their extension values under shared
    challenges, so each submitted row gives its RAM outputs from the tokens of that permutation. -/
def UnrolledReducedFromNativePermutation : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables →
    NativePublicSetup.CoversROM cells →
    ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
      (certificates : List (ProgramLogicalRowCertificate tables)) (values : List (GKRAddress → E)),
      UnrolledPermutationArguments challenges tables certificates values trace workers →
      RVRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)

/-- One submitted CPU row meets the exact public boot premises, its extension values and the single RAM permutation. -/
def UnrolledReducedFromNativePermutationSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    NativePublicSetup.CoversROM cells ∧
    ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (certificates : List (ProgramLogicalRowCertificate tables))
      (values : List (GKRAddress → NativeArithmetic.F)),
      UnrolledPermutationArguments challenges tables certificates values trace workers ∧
      trace.rows.length = 1 ∧ workers.standard.rows = [] ∧ workers.split.rows = []

/-- The premises of `UnifiedFromNative`, with the single native RAM permutation of the production prover as the only
    matching premise, give its result. The certificates carry their extension values under shared challenges, so
    each submitted row gives its RAM outputs from the tokens of that permutation. -/
def UnifiedFromNativePermutation : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits →
    NoSpecial5 program →
    UnifiedStreamPorts trace initial.input →
    NativePublicSetup.Bound initial program tables →
    ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
      (certificates : List (UnifiedLogicalRowCertificate tables)) (values : List (GKRAddress → E)),
      UnifiedPermutationArguments challenges tables certificates values trace workers →
      RVRealizes trace initial cells (unifiedReadCount trace)

/-- A loop trace with sixteen CPU rows and two worker rows meets the exact public boot premises, their extension
    values and the single RAM permutation. -/
def UnifiedFromNativePermutationSatisfiableClaim : Prop :=
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    NoSpecial5 program ∧
    UnifiedStreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (certificates : List (UnifiedLogicalRowCertificate tables))
      (values : List (GKRAddress → NativeArithmetic.F)),
      UnifiedPermutationArguments challenges tables certificates values trace workers ∧
      trace.rows.length = 16 ∧ workers.standard.rows.length = 2 ∧ workers.split.rows = []

/-- The premises of `PaddedUnrolledFullFromNative`, with the single native masked RAM permutation of the production
    prover as the only matching premise, give its result. The certificates carry their extension values under shared
    challenges, so each submitted row gives its RAM outputs from the tokens of that permutation. -/
def PaddedUnrolledFullFromNativePermutation : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned (active trace) initial cells program InitsTeardowns.importedLayout inits →
    NoSpecial5 program →
    NonDeterminism.Pooled.StreamPorts (active trace) initial.input →
    NativePublicSetup.Bound initial program tables →
    NativePublicSetup.CoversROM cells →
    ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
      (certificates : List (ProgramRowCertificate tables)) (values : List (GKRAddress → E)),
      PaddedUnrolledPermutationArguments challenges tables certificates values trace workers →
      RVRealizes trace initial cells (NonDeterminism.Pooled.readCount (active trace))

/-- One active CPU row and one padding CPU row meet the padded premises, their extension values and the single
    masked RAM permutation. -/
def PaddedUnrolledFullFromNativePermutationSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned (active trace) initial cells program InitsTeardowns.importedLayout inits ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts (active trace) initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    NativePublicSetup.CoversROM cells ∧
    ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (certificates : List (ProgramRowCertificate tables))
      (values : List (GKRAddress → NativeArithmetic.F)),
      PaddedUnrolledPermutationArguments challenges tables certificates values trace workers ∧
      (active trace).rows.length = 1 ∧ (inactive trace).rows.length = 1

/-- The premises of `PaddedUnrolledReducedFromNative`, with the single native masked RAM permutation of the
    production prover as the only matching premise, give its result. The certificates carry their extension values
    under shared challenges, so each submitted row gives its RAM outputs from the tokens of that permutation. -/
def PaddedUnrolledReducedFromNativePermutation : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced (active trace) initial cells program InitsTeardowns.importedLayout inits →
    NonDeterminism.Pooled.StreamPorts (active trace) initial.input →
    NativePublicSetup.Bound initial program tables →
    NativePublicSetup.CoversROM cells →
    ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
      (certificates : List (ProgramRowCertificate tables)) (values : List (GKRAddress → E)),
      PaddedUnrolledPermutationArguments challenges tables certificates values trace workers →
      RVRealizes trace initial cells (NonDeterminism.Pooled.readCount (active trace))

/-- One active CPU row and one padding CPU row meet the padded premises, their extension values and the single
    masked RAM permutation. -/
def PaddedUnrolledReducedFromNativePermutationSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced (active trace) initial cells program InitsTeardowns.importedLayout inits ∧
    NonDeterminism.Pooled.StreamPorts (active trace) initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    NativePublicSetup.CoversROM cells ∧
    ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (certificates : List (ProgramRowCertificate tables))
      (values : List (GKRAddress → NativeArithmetic.F)),
      PaddedUnrolledPermutationArguments challenges tables certificates values trace workers ∧
      (active trace).rows.length = 1 ∧ (inactive trace).rows.length = 1

/-- The premises of `PaddedUnifiedFromNative`, with the single native masked RAM permutation of the production
    prover as the only matching premise, give its result. The certificates carry their extension values under shared
    challenges, so each submitted row gives its RAM outputs from the tokens of that permutation. -/
def PaddedUnifiedFromNativePermutation : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified (active trace) initial cells program InitsTeardowns.unifiedLayout inits →
    NoSpecial5 program →
    UnifiedStreamPorts (active trace) initial.input →
    NativePublicSetup.Bound initial program tables →
    ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
      (certificates : List (UnifiedRowCertificate tables)) (values : List (GKRAddress → E)),
      PaddedUnifiedPermutationArguments challenges tables certificates values trace workers →
      RVRealizes trace initial cells (unifiedReadCount (active trace))

/-- One active unified row and one padding row meet the padded premises, their extension values and the single
    masked RAM permutation. -/
def PaddedUnifiedFromNativePermutationSatisfiableClaim : Prop :=
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified (active trace) initial cells program InitsTeardowns.unifiedLayout inits ∧
    NoSpecial5 program ∧
    UnifiedStreamPorts (active trace) initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (certificates : List (UnifiedRowCertificate tables))
      (values : List (GKRAddress → NativeArithmetic.F)),
      PaddedUnifiedPermutationArguments challenges tables certificates values trace workers ∧
      (active trace).rows.length = 1 ∧ (inactive trace).rows.length = 1

end Airbender.Trace.Machine.Native
