module
public import Human.Compiler.MemoryPorts
public import Human.Compiler.WorkerMemoryPorts
public import Human.Trace.Machine.Model
public import Human.Helpers.Delegation.RVDecoder
public import Human.Helpers.UnifiedReduced.RVRequestTrace

@[expose] public section
namespace Airbender.Compiler.NativeMemory
open Trace Trace.Machine

/-- The address space of a native token address: zero for registers, one for RAM, two for PC states. -/
def space (address : Nat) : Nat := (Nat.unpair address).1

/-- The first limb of a native token address. It is the register index of a register address. -/
def registerIndex (address : Nat) : Nat := (Nat.unpair (Nat.unpair address).2).1

/-- A RAM address, or a register address below 32. Request tokens use register indices from 32 up. -/
def Architectural (address : Nat) : Prop :=
  space address = 1 ∨ (space address = 0 ∧ registerIndex address < 32)

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
    the native machine arguments. The boot inputs place the seeds and final tokens at registers and RAM.
    The binding of each selected caller gives its request port tokens. The architectural ports of every CPU row
    address RAM or registers below 32. -/
def UnrolledMemoryCompositionClaim : Prop :=
  ∀ (config : RVMachineConfig) (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)),
    BootInputs config trace initial cells program layout inits →
    (∀ row ∈ unrolledCallers trace, ∃ (before : RV.State) (callers : List Delegation.Caller.RVProgramEntry),
      Delegation.Caller.RVBinding row.assignment before callers) →
    (∀ row ∈ trace.rows, ∀ port ∈ Delegation.Caller.machinePorts row,
      NativeMemory.Architectural (port.address.code row.assignment)) →
    NativeMemory.RamPermutation trace workers →
    (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start) ∧
    Delegation.Requests.Matching ((unrolledCallers trace).map fun row => Delegation.Requests.caller row.assignment)
      workers.fulfillments ∧
    (trace.initialMemory ++ (unrolledSteps trace ++ workers.steps).map Prod.snd).Perm
      (trace.terminalMemory ++ (unrolledSteps trace ++ workers.steps).map Prod.fst)

/-- One ADD row with its boot inputs meets the premises of the unrolled composition. -/
def UnrolledMemoryCompositionSatisfiableClaim : Prop :=
  ∃ (config : RVMachineConfig) (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)),
    trace.rows.length = 1 ∧
    BootInputs config trace initial cells program layout inits ∧
    (∀ row ∈ unrolledCallers trace, ∃ (before : RV.State) (callers : List Delegation.Caller.RVProgramEntry),
      Delegation.Caller.RVBinding row.assignment before callers) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ Delegation.Caller.machinePorts row,
      NativeMemory.Architectural (port.address.code row.assignment)) ∧
    NativeMemory.RamPermutation trace workers

/-- The single native RAM permutation of a unified trace gives the state, request and memory relations of
    the native machine arguments. The boot inputs place the seeds and final tokens at registers and RAM.
    The binding of each selected caller gives its request port tokens. The architectural ports of every CPU row
    address RAM or registers below 32. -/
def UnifiedMemoryCompositionClaim : Prop :=
  ∀ (config : RVMachineConfig) (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)),
    BootInputs config trace initial cells program layout inits →
    (∀ row ∈ trace.rows, UnifiedReduced.Caller.Selected row.assignment →
      ∃ (before : RV.State) (callers : List Delegation.Caller.RVProgramEntry),
        UnifiedReduced.Caller.RVBinding row.assignment before callers) →
    (∀ row ∈ trace.rows, ∀ port ∈ UnifiedReduced.Caller.machinePorts row,
      NativeMemory.Architectural (port.address.code row.assignment)) →
    NativeMemory.RamPermutation trace workers →
    (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start) ∧
    Delegation.Requests.Matching
      ((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
        fun row => UnifiedReduced.Caller.request row.assignment) workers.fulfillments ∧
    (trace.initialMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.snd).Perm
      (trace.terminalMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.fst)

/-- One unified row with its boot inputs meets the premises of the unified composition. -/
def UnifiedMemoryCompositionSatisfiableClaim : Prop :=
  ∃ (config : RVMachineConfig) (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)),
    trace.rows ≠ [] ∧
    BootInputs config trace initial cells program layout inits ∧
    (∀ row ∈ trace.rows, UnifiedReduced.Caller.Selected row.assignment →
      ∃ (before : RV.State) (callers : List Delegation.Caller.RVProgramEntry),
        UnifiedReduced.Caller.RVBinding row.assignment before callers) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ UnifiedReduced.Caller.machinePorts row,
      NativeMemory.Architectural (port.address.code row.assignment)) ∧
    NativeMemory.RamPermutation trace workers

end Airbender.Compiler
