module
public import Proven.Trace.Machine.UnrolledWriteRules
public import Proven.Trace.Machine.UnifiedWriteRules
public import Proven.Delegation.RVSharedOperations

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The shared unrolled history bounds every CPU/worker read, write and terminal word from the public seed image. -/
theorem unrolled_memory_bounds {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (programImage : rvMachineProgramImage config initialState addresses = some program)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initialState cells))
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initialState))
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows) :
    (∀ edge ∈ (unrolledMemory trace workers).steps, edge.1.word.Bounded ∧ edge.2.word.Bounded) ∧
      ∀ token ∈ trace.terminalMemory, token.word.Bounded := by
  have facts := unrolled_memory_facts accepted initial aligned image
  have rules := unrolled_write_rules unrolled accepted initial aligned programImage wordSetup subwordSetup tables
  exact Delegation.Caller.Proofs.rv_transfer_bounds facts (RVValues.rv_image_bounds image) rules

/-- The shared unified history bounds every CPU/worker read, write and terminal word from the public seed image. -/
theorem unified_memory_bounds {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState : RV.State} {cells : List Cell}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows) :
    (∀ edge ∈ (unifiedMemory trace workers).steps, edge.1.word.Bounded ∧ edge.2.word.Bounded) ∧
      ∀ token ∈ trace.terminalMemory, token.word.Bounded :=
  Delegation.Caller.Proofs.rv_transfer_bounds (unified_memory_facts accepted initial aligned image)
    (RVValues.rv_image_bounds image) (unified_write_rules accepted initial aligned tables)

end Airbender.Trace.Machine.Proofs
