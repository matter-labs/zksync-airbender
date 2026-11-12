module
public import Human.Helpers.Decoder.RVMachineProgram
public import Human.Helpers.Context.RVPooledBoundary
public import Human.Helpers.Context.VerifierBoundary.Theorems
public import Human.Helpers.Delegation.MixedMemory
public import Human.Helpers.UnifiedReduced.RVMixedMemory
public import Human.Helpers.UnifiedReduced.RVExecutionInputs
public import Human.Circuits.KeccakSplit.Native
public import Human.Trace.RVExecution

@[expose] public section

namespace Airbender.Trace.Machine
open Delegation

/-- All submitted worker rows. Their boundary tokens are supplied by the shared machine permutation. -/
structure WorkerPools (p : Nat) where
  /-- Bigint, G, round and special5 assignments. -/
  standard : Delegation.MemoryData p
  /-- The three split Keccak assignments. -/
  split : Keccak.Split.Native.MemoryData p

/-- All architectural worker transfers. -/
def WorkerPools.steps (workers : WorkerPools p) := workers.standard.steps ++ workers.split.steps

/-- Split-worker request identity from its full CSR and imported invocation columns. -/
def splitFulfillment (row : Keccak.Split.Native.Row p) : Requests.Request p :=
  ⟨match row.kind with
    | .columnParity => 0x7cd
    | .thetaRho => 0x7cc
    | .chi5 => 0x7ce,
    rawPair row.assignment row.columns.invocation⟩

/-- The complete submitted fulfillment list. -/
def WorkerPools.fulfillments (workers : WorkerPools p) :=
  workers.standard.rows.map Requests.fulfillment ++ workers.split.rows.map splitFulfillment

/-- Every worker row satisfies its imported equations, lookups and participation flag. -/
structure WorkersAccepted [Fact p.Prime] (workers : WorkerPools p) : Prop where
  /-- The standard worker assignments satisfy their imported constraints. -/
  standardConstraints : ∀ row ∈ workers.standard.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints workers.standard.setup)
  /-- Each standard worker participates. -/
  standardActive : ∀ row ∈ workers.standard.rows, row.assignment row.columns.execute = 1
  /-- The split worker assignments satisfy their imported constraints and native fixed tables. -/
  splitConstraints : ∀ row ∈ workers.split.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints
  /-- Each split worker participates. -/
  splitActive : ∀ row ∈ workers.split.rows, row.assignment row.columns.execute = 1

/-- One native CPU query is in the public program table of its circuit family. -/
def Decoded (family : RVMachineDecoderFamily) (query : Vector (ZMod p) 9)
    (program : List RVMachineProgramEntry) : Prop :=
  ∃ entry ∈ program, entry.data.family = family ∧
    query = (entry.data.row entry.pc).map (fun (value : Nat) => (value : ZMod p))

/-- The selected unrolled delegation caller rows. -/
def unrolledCallers [Fact p.Prime] (trace : PooledTrace p) :=
  trace.rows.filter fun row => row.family == .addSub && decide (Requests.Selected row.assignment)

/-- All architectural unrolled transfers. Virtual CSR ports belong to request matching. -/
def unrolledSteps [Fact p.Prime] (trace : PooledTrace p) :=
  trace.rows.flatMap fun row => (Delegation.Caller.machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)

/-- The unrolled native acceptance boundary. Cached-layer preservation discharges the imported constraints.
    Decoder membership, request matching, raw state matching and shared memory matching remain explicit here. -/
structure UnrolledAcceptance [Fact p.Prime] (trace : PooledTrace p) (workers : WorkerPools p)
    (program : List RVMachineProgramEntry) : Prop extends WorkersAccepted workers where
  /-- Every CPU assignment satisfies its imported constraints. -/
  constraints : ∀ row ∈ trace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom)
  /-- Each selected CPU row participates. -/
  active : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 1
  /-- The raw CPU state tuples balance. -/
  states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start)
  /-- Every native CPU query belongs to its public program table. -/
  decoded : ∀ row ∈ trace.rows, Decoded (.pooled row.family) row.decoderQuery program
  /-- All callers and all submitted workers share the native request permutation. -/
  requests : Requests.Matching ((unrolledCallers trace).map fun row => Requests.caller row.assignment)
    workers.fulfillments
  /-- Architectural CPU and worker tokens share one initialized memory permutation. -/
  memory : (trace.initialMemory ++ (unrolledSteps trace ++ workers.steps).map Prod.snd).Perm
    (trace.terminalMemory ++ (unrolledSteps trace ++ workers.steps).map Prod.fst)

/-- All architectural unified transfers, with virtual request ports removed. -/
def unifiedSteps [Fact p.Prime] (trace : UnifiedTrace p) :=
  trace.rows.flatMap fun row => (UnifiedReduced.Caller.machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)

/-- The unified native acceptance boundary over the same public program and shared worker pool. -/
structure UnifiedAcceptance [Fact p.Prime] (trace : UnifiedTrace p) (workers : WorkerPools p)
    (program : List RVMachineProgramEntry) : Prop extends WorkersAccepted workers where
  /-- Every CPU assignment satisfies its imported constraints. -/
  constraints : ∀ row ∈ trace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom)
  /-- Each selected CPU row participates. -/
  active : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 1
  /-- The raw CPU state tuples balance. -/
  states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start)
  /-- Every native CPU query belongs to the public unified program table. -/
  decoded : ∀ row ∈ trace.rows, Decoded .unified row.decoderQuery program
  /-- All unified callers and all submitted workers share the request permutation. -/
  requests : Requests.Matching
    ((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) workers.fulfillments
  /-- Architectural CPU and worker tokens share one initialized memory permutation. -/
  memory : (trace.initialMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.snd).Perm
    (trace.terminalMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.fst)

/-- Public boot data. No operand, result, execution or terminal-PC range is supplied. -/
structure BootInputs {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (config : RVMachineConfig) (trace : Data p Kind) (initial : RV.State) (cells : List Cell)
    (program : List RVMachineProgramEntry) (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness p layout)) : Prop where
  /-- Each tracked cell occurs once. -/
  distinct : cells.Nodup
  /-- Tracked RAM cells are aligned. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- The architectural machine starts at PC zero. -/
  pc : initial.pc = 0
  /-- All public initial register values are zero. -/
  registersZero : ∀ index, (Cell.register index).readRV initial = some 0
  /-- Public ROM bytes and the production projection construct the program. -/
  programImage : ∃ addresses, rvMachineProgramImage config initial addresses = some program
  /-- All initialization instances pass the full statement verifier's top-bits check. -/
  topBits : InitsTeardowns.TopBitsChecked (inits.flatMap fun w => w.topBits.toList)
  /-- Native seeds contain the register seeds and every initialization instance. -/
  seeds : trace.initialMemory = registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens
  /-- The tracked domain is the registers and all initialized windows. -/
  domain : cells = registerCells ++
    InitsTeardowns.windowCells layout (inits.flatMap fun w => w.topBits.toList)
  /-- The native seeds are reads of the public initial state. -/
  image : initialImageRV initial cells = some trace.initialMemory
  /-- The native machine starts at PC zero and clock four. -/
  initialBoundary : trace.initial = PCState.boundary 0 (4, 0)
  /-- The typed full statement verifier contribution closes the raw PC-state permutation. -/
  stateClosure : VerifierBoundary.BootClosure trace.initial (trace.rows.map Row.start) (trace.rows.map Row.finish)

/-- The public program does not call the special5 circuit. -/
def NoSpecial5 (program : List RVMachineProgramEntry) : Prop :=
  ∀ entry ∈ program, RV.decode entry.bits ≠ some (.delegate .keccak)

end Airbender.Trace.Machine
