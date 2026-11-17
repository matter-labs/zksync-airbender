module
public import Human.Compiler.MemoryPorts
public import Human.Compiler.WorkerMemoryPorts
public import Human.Compiler.NativePublicSetup
public import Human.Trace.Machine.Model

@[expose] public section
namespace Airbender.Compiler.NativeMemory
open Trace Trace.Machine

/-- Every worker row reads its port tokens and its issued request token. -/
def workerReads (workers : WorkerPools babyBearModulus) : List (MemoryToken babyBearModulus) :=
  workers.standard.rows.flatMap standardReads ++ workers.split.rows.flatMap splitReads

/-- Every worker row writes its port tokens and its returned request token. -/
def workerWrites (workers : WorkerPools babyBearModulus) : List (MemoryToken babyBearModulus) :=
  workers.standard.rows.flatMap standardWrites ++ workers.split.rows.flatMap splitWrites

/-- The single native RAM permutation of a CPU trace and its workers. The initial PC state, the seeds, every CPU
    write and every worker write match the terminal PC state, the final tokens, every CPU read and every worker
    read. The CPU and worker tokens are the tokens of the RAM output claims. -/
def RamPermutation {Kind : Type} [CircuitLayout Kind] (trace : Data babyBearModulus Kind)
    (workers : WorkerPools babyBearModulus) : Prop :=
  (stateToken trace.initial :: trace.initialMemory ++ trace.rows.flatMap cpuWrites ++ workerWrites workers).Perm
    (stateToken trace.terminal :: trace.terminalMemory ++ trace.rows.flatMap cpuReads ++ workerReads workers)

end Airbender.Compiler.NativeMemory

namespace Airbender.Compiler
open Trace Trace.Machine

/-- The single native RAM permutation of an unrolled trace gives the state, request and memory relations of
    the native machine arguments. The native CPU certificates of the submitted rows, the public program and the
    boot inputs place every token in one address class: PC states, delegation requests, or registers and RAM. -/
def UnrolledMemoryCompositionClaim : Prop :=
  ∀ (config : RVMachineConfig) (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)) (tables : ProgramLookupRows)
    (certificates : List (ProgramLogicalRowCertificate tables)),
    config ≠ .unified →
    BootInputs config trace initial cells program layout inits →
    NativePublicSetup.Bound initial program tables → NativePublicSetup.CoversROM cells →
    trace.rows = certificates.map (·.row) →
    NativeMemory.RamPermutation trace workers →
    (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start) ∧
    Delegation.Requests.Matching ((unrolledCallers trace).map fun row => Delegation.Requests.caller row.assignment)
      workers.fulfillments ∧
    (trace.initialMemory ++ (unrolledSteps trace ++ workers.steps).map Prod.snd).Perm
      (trace.terminalMemory ++ (unrolledSteps trace ++ workers.steps).map Prod.fst)

/-- One ADD row with its boot inputs and native certificate meets the premises of the unrolled composition. -/
def UnrolledMemoryCompositionSatisfiableClaim : Prop :=
  ∃ (config : RVMachineConfig) (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)) (tables : ProgramLookupRows)
    (certificates : List (ProgramLogicalRowCertificate tables)),
    config ≠ .unified ∧
    BootInputs config trace initial cells program layout inits ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    trace.rows = certificates.map (·.row) ∧
    NativeMemory.RamPermutation trace workers ∧
    trace.rows.length = 1

/-- The single native RAM permutation of a unified trace gives the state, request and memory relations of the
    native machine arguments. The native unified certificates of the submitted rows, the public program and the
    boot inputs place every token in one address class: PC states, delegation requests, or registers and RAM. -/
def UnifiedMemoryCompositionClaim : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)) (tables : ProgramLookupRows)
    (certificates : List (UnifiedLogicalRowCertificate tables)),
    BootInputs .unified trace initial cells program layout inits →
    NativePublicSetup.Bound initial program tables →
    trace.rows = certificates.map (·.row) →
    NativeMemory.RamPermutation trace workers →
    (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start) ∧
    Delegation.Requests.Matching
      ((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
        fun row => UnifiedReduced.Caller.request row.assignment) workers.fulfillments ∧
    (trace.initialMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.snd).Perm
      (trace.terminalMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.fst)

/-- A loop with sixteen unified rows and two bigint calls meets the premises of the unified composition. -/
def UnifiedMemoryCompositionSatisfiableClaim : Prop :=
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)) (tables : ProgramLookupRows)
    (certificates : List (UnifiedLogicalRowCertificate tables)),
    BootInputs .unified trace initial cells program layout inits ∧
    NativePublicSetup.Bound initial program tables ∧
    trace.rows = certificates.map (·.row) ∧
    NativeMemory.RamPermutation trace workers ∧
    trace.rows.length = 16 ∧ workers.standard.rows.length = 2

end Airbender.Compiler
