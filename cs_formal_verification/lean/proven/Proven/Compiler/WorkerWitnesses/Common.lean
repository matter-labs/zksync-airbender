module
public import Human.Compiler.WorkerCertificates

@[expose] public section
namespace Airbender.Compiler.WorkerWitnesses
open NativeArithmetic
set_option warningAsError true

/-- An arithmetic extension and lookup refinement construct a full native worker certificate. -/
noncomputable def ofExtension (family : NativeWorkerLookups.Family) (logical : Nat → F)
    (native : ∃ physical : GKRAddress → F,
      Holds (NativeWorkerLookups.circuitFor family) physical ∧
        PlacementAgreement (NativeWorkerLookups.circuitFor family) physical logical)
    (lookups : ∀ physical, PlacementAgreement (NativeWorkerLookups.circuitFor family) physical logical →
      NativeLookups.Arguments (NativeWorkerLookups.circuitFor family)
        (NativeWorkerLookups.selectorsFor family) physical (NativeWorkerSetup.rows family))
    (active : logical (workerColumns family).execute = 1) : WorkerCertificate where
  family := family
  assignment := logical
  physical := Classical.choose native
  arithmetic := (Classical.choose_spec native).1
  placement := (Classical.choose_spec native).2
  lookups := lookups _ (Classical.choose_spec native).2
  active := active

end Airbender.Compiler.WorkerWitnesses
