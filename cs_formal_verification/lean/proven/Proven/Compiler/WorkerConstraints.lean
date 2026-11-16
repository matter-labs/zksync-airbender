module
public import Proven.Compiler.WorkerConstraints.Bigint
public import Proven.Compiler.WorkerConstraints.BlakeG
public import Proven.Compiler.WorkerConstraints.BlakeRound
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho
public import Proven.Compiler.WorkerConstraints.KeccakChi5
public import Proven.Compiler.NativeBindings.Bigint
public import Proven.Compiler.NativeBindings.BlakeG
public import Proven.Compiler.NativeBindings.BlakeRound
public import Proven.Compiler.WorkerBindings.KeccakColumnParity
public import Proven.Compiler.WorkerBindings.KeccakThetaRho
public import Proven.Compiler.WorkerBindings.KeccakChi5

@[expose] public section
namespace Airbender.Compiler.WorkerConstraints
open NativeArithmetic NativeWorkerLookups
set_option warningAsError true

/-- Native cached gates, source placement and public lookup matching imply the full worker description. -/
theorem certificate_constraints (entry : WorkerCertificate) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment entry.assignment)
      (constraints entry.family) := by
  obtain ⟨family, logical, physical, arithmetic, placement, arguments, _active⟩ := entry
  cases family
  · exact holds_of_lookups .bigint logical
      (NativeBindings.Bigint.arithmetic physical logical arithmetic placement)
      (Bigint.lookups physical logical placement arguments)
  · exact holds_of_lookups .blakeG logical
      (NativeBindings.BlakeG.arithmetic physical logical arithmetic placement)
      (BlakeG.lookups physical logical placement arguments)
  · exact holds_of_lookups .blakeRound logical
      (NativeBindings.BlakeRound.arithmetic physical logical arithmetic placement)
      (BlakeRound.lookups physical logical placement arguments)
  · exact holds_of_lookups .columnParity logical
      (WorkerBindings.KeccakColumnParity.arithmetic physical logical arithmetic placement)
      (KeccakColumnParity.lookups physical logical placement arguments)
  · exact holds_of_lookups .thetaRho logical
      (WorkerBindings.KeccakThetaRho.arithmetic physical logical arithmetic placement)
      (KeccakThetaRho.lookups physical logical placement arguments)
  · exact holds_of_lookups .chi5 logical
      (WorkerBindings.KeccakChi5.arithmetic physical logical arithmetic placement)
      (KeccakChi5.lookups physical logical placement arguments)

/-- A represented standard row has the canonical description constraints and its native participation flag. -/
theorem standard_facts (entry : WorkerCertificate) (row : Delegation.Row babyBearModulus)
    (represented : entry.standardRow = some row) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints (Delegation.modeledSetup Keccak.Controller.rows)) ∧
      row.assignment row.columns.execute = 1 := by
  have full := certificate_constraints entry
  have active := entry.active
  obtain ⟨family, _logical, _physical, _arithmetic, _placement, _arguments, _participation⟩ := entry
  cases family <;> cases represented
  all_goals exact ⟨full, active⟩

/-- A represented split row has its full native description and participation flag. -/
theorem split_facts (entry : WorkerCertificate) (row : Keccak.Split.Native.Row babyBearModulus)
    (represented : entry.splitRow = some row) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints ∧
      row.assignment row.columns.execute = 1 := by
  have full := certificate_constraints entry
  have active := entry.active
  obtain ⟨family, _logical, _physical, _arithmetic, _placement, _arguments, _participation⟩ := entry
  cases family <;> cases represented
  all_goals exact ⟨full, active⟩

/-- Exact submitted-row certificates derive the worker description boundary from public setup tables. -/
theorem accepted (workers : Trace.Machine.WorkerPools babyBearModulus)
    (certified : WorkerRowsCertified workers)
    (setup : workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows) :
    Trace.Machine.WorkersAccepted workers := by
  obtain ⟨certificates, standard, split⟩ := certified
  constructor
  · intro row member
    rw [setup]
    rw [standard] at member
    obtain ⟨entry, _present, represented⟩ := List.mem_filterMap.mp member
    exact (standard_facts entry row represented).1
  · intro row member
    rw [standard] at member
    obtain ⟨entry, _present, represented⟩ := List.mem_filterMap.mp member
    exact (standard_facts entry row represented).2
  · intro row member
    rw [split] at member
    obtain ⟨entry, _present, represented⟩ := List.mem_filterMap.mp member
    exact (split_facts entry row represented).1
  · intro row member
    rw [split] at member
    obtain ⟨entry, _present, represented⟩ := List.mem_filterMap.mp member
    exact (split_facts entry row represented).2

end Airbender.Compiler.WorkerConstraints
