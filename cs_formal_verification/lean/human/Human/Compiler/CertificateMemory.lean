module
public import Human.Compiler.MemoryPorts
public import Human.Compiler.WorkerMemoryPorts
public import Human.Compiler.NativeMachineArguments

@[expose] public section
namespace Airbender.Compiler
open Trace

/-- Extension values of cached CPU certificates under one shared challenge set, in certificate order. Each value
    map meets the extension semantics of the capture of its certificate at the physical values of that
    certificate. -/
def ProgramExtensions {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) {tables : ProgramLookupRows}
    (certificates : List (ProgramRowCertificate tables)) (values : List (GKRAddress → E)) : Prop :=
  List.Forall₂ (fun certificate values => NativeMemory.Holds (NativeLookups.circuitFor (.pooled certificate.row.family))
    challenges certificate.physical values) certificates values

/-- Extension values of cached unified certificates under one shared challenge set, in certificate order. -/
def UnifiedExtensions {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) {tables : ProgramLookupRows}
    (certificates : List (UnifiedRowCertificate tables)) (values : List (GKRAddress → E)) : Prop :=
  List.Forall₂ (fun certificate values => NativeMemory.Holds (NativeLookups.circuitFor .unified)
    challenges certificate.physical values) certificates values

/-- Native worker certificates with extension values under the shared challenges describe exactly each submitted
    worker pool, in its submitted order. -/
def WorkerRowsExtended {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (workers : Trace.Machine.WorkerPools babyBearModulus) : Prop :=
  ∃ (certificates : List WorkerCertificate) (values : List (GKRAddress → E)),
    List.Forall₂ (fun (certificate : WorkerCertificate) values =>
      NativeMemory.Holds (NativeWorkerLookups.circuitFor certificate.family) challenges certificate.physical values)
      certificates values ∧
    workers.standard.rows = certificates.filterMap (·.standardRow) ∧
    workers.split.rows = certificates.filterMap (·.splitRow)

/-- Native worker certificates with extension values under the shared challenges describe exactly each submitted
    worker pool, in its submitted order. Each execute selector is Boolean. -/
def PaddedWorkerRowsExtended {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (workers : Trace.Machine.WorkerPools babyBearModulus) : Prop :=
  ∃ (certificates : List WorkerRowCertificate) (values : List (GKRAddress → E)),
    List.Forall₂ (fun (certificate : WorkerRowCertificate) values =>
      NativeMemory.Holds (NativeWorkerLookups.circuitFor certificate.family) challenges certificate.physical values)
      certificates values ∧
    (∀ certificate ∈ certificates, certificate.assignment (workerColumns certificate.family).execute = 0 ∨
      certificate.assignment (workerColumns certificate.family).execute = 1) ∧
    workers.standard.rows = certificates.filterMap (·.standardRow) ∧
    workers.split.rows = certificates.filterMap (·.splitRow)

/-- The extension values of a cached CPU certificate give the RAM outputs of its row: the execute-masked
    products of its port tokens and PC-state tokens. -/
def ProgramCertificateRamProductsClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (tables : ProgramLookupRows)
    (certificate : ProgramRowCertificate tables) (values : GKRAddress → E),
    NativeMemory.Holds (NativeLookups.circuitFor (.pooled certificate.row.family)) challenges certificate.physical values →
    NativeMemory.RamProducts (NativeLookups.circuitFor (.pooled certificate.row.family)) challenges values
      (certificate.row.assignment certificate.row.columns.execute) (NativeMemory.cpuReads certificate.row)
      (NativeMemory.cpuWrites certificate.row)

/-- One cached CPU certificate has extension values for its physical values. -/
def ProgramCertificateRamProductsSatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (tables : ProgramLookupRows)
    (certificate : ProgramRowCertificate tables) (values : GKRAddress → NativeArithmetic.F),
    NativeMemory.Holds (NativeLookups.circuitFor (.pooled certificate.row.family)) challenges certificate.physical values

/-- The extension values of a cached unified certificate give the RAM outputs of its row: the execute-masked
    products of its port tokens and PC-state tokens. -/
def UnifiedCertificateRamProductsClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (tables : ProgramLookupRows)
    (certificate : UnifiedRowCertificate tables) (values : GKRAddress → E),
    NativeMemory.Holds (NativeLookups.circuitFor .unified) challenges certificate.physical values →
    NativeMemory.RamProducts (NativeLookups.circuitFor .unified) challenges values
      (certificate.row.assignment certificate.row.columns.execute) (NativeMemory.cpuReads certificate.row)
      (NativeMemory.cpuWrites certificate.row)

/-- One cached unified certificate has extension values for its physical values. -/
def UnifiedCertificateRamProductsSatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (tables : ProgramLookupRows)
    (certificate : UnifiedRowCertificate tables) (values : GKRAddress → NativeArithmetic.F),
    NativeMemory.Holds (NativeLookups.circuitFor .unified) challenges certificate.physical values

/-- The extension values of a cached worker certificate give the RAM outputs of its standard or split row: the
    execute-masked products of its port tokens and request tokens. -/
def WorkerCertificateRamProductsClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (certificate : WorkerRowCertificate)
    (values : GKRAddress → E),
    NativeMemory.Holds (NativeWorkerLookups.circuitFor certificate.family) challenges certificate.physical values →
    (∀ row, certificate.standardRow = some row →
      NativeMemory.RamProducts (NativeWorkerLookups.circuitFor certificate.family) challenges values
        (row.assignment row.columns.execute) (NativeMemory.standardReads row) (NativeMemory.standardWrites row)) ∧
    (∀ row, certificate.splitRow = some row →
      NativeMemory.RamProducts (NativeWorkerLookups.circuitFor certificate.family) challenges values
        (row.assignment row.columns.execute) (NativeMemory.splitReads row) (NativeMemory.splitWrites row))

/-- One cached worker certificate has extension values for its physical values. -/
def WorkerCertificateRamProductsSatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (certificate : WorkerRowCertificate)
    (values : GKRAddress → NativeArithmetic.F),
    NativeMemory.Holds (NativeWorkerLookups.circuitFor certificate.family) challenges certificate.physical values

end Airbender.Compiler
