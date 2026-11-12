module
public import Human.Trace.Machine.Theorems
public import Human.Helpers.Context.PaddingBoundary.Theorems

@[expose] public section
namespace Airbender.Trace.Machine
open Delegation PaddingBoundary

/-- Select each worker solely by its native execute column. -/
def activeWorkers (workers : WorkerPools p) : WorkerPools p :=
  ⟨{ workers.standard with rows := workers.standard.rows.filter fun row => decide (row.assignment row.columns.execute = 1) },
   { workers.split with rows := workers.split.rows.filter fun row => decide (row.assignment row.columns.execute = 1) }⟩

/-- Mask each unrolled architectural token with its CPU row selector. -/
def maskedUnrolledTokens [Fact p.Prime] (trace : PooledTrace p) (token : (MemoryToken p × MemoryToken p) → MemoryToken p) :=
  contributions trace.rows (fun row => row.assignment row.columns.execute) fun row =>
    (Delegation.Caller.machinePorts row).toList.map fun port => token
      (readToken row.assignment port, writeToken row.columns row.assignment port)

/-- Mask each unified architectural token with its CPU row selector. -/
def maskedUnifiedTokens [Fact p.Prime] (trace : UnifiedTrace p) (token : (MemoryToken p × MemoryToken p) → MemoryToken p) :=
  contributions trace.rows (fun row => row.assignment row.columns.execute) fun row =>
    (UnifiedReduced.Caller.machinePorts row).toList.map fun port => token
      (readToken row.assignment port, writeToken row.columns row.assignment port)

/-- Mask all worker architectural tokens with their own selectors. -/
def maskedWorkerTokens (workers : WorkerPools p) (token : (MemoryToken p × MemoryToken p) → MemoryToken p) :=
  contributions workers.standard.rows (fun row => row.assignment row.columns.execute)
    (fun row => row.memorySteps.map token) ++
  contributions workers.split.rows (fun row => row.assignment row.columns.execute)
    (fun row => row.memorySteps.map token)

/-- Mask complete unrolled request tokens; the CSR and raw clock stay intact. -/
def maskedUnrolledRequests [Fact p.Prime] (trace : PooledTrace p) (token : Requests.Request p → MemoryToken p) :=
  contributions (unrolledCallers trace) (fun row => row.assignment row.columns.execute)
    (fun row => [token (Requests.caller row.assignment)])

/-- Mask complete unified request tokens. -/
def maskedUnifiedRequests [Fact p.Prime] (trace : UnifiedTrace p) (token : Requests.Request p → MemoryToken p) :=
  contributions (trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment))
    (fun row => row.assignment row.columns.execute) (fun row => [token (UnifiedReduced.Caller.request row.assignment)])

/-- Mask each submitted worker request and its returned zero-clock token. -/
def maskedWorkerRequests (workers : WorkerPools p) (token : Requests.Request p → MemoryToken p) :=
  contributions workers.standard.rows (fun row => row.assignment row.columns.execute)
    (fun row => [token (Requests.fulfillment row)]) ++
  contributions workers.split.rows (fun row => row.assignment row.columns.execute)
    (fun row => [token (splitFulfillment row)])

/-- All worker constraints hold, including the constraints of inactive rows. -/
structure MaskedWorkersAccepted [Fact p.Prime] (workers : WorkerPools p) : Prop where
  /-- Every standard assignment satisfies the imported constraints. -/
  standardConstraints : ∀ row ∈ workers.standard.rows, FlatOperation.ConstraintsHoldFlat
    (Verification.environment row.assignment) (row.constraints workers.standard.setup)
  /-- Every split assignment satisfies the imported constraints. -/
  splitConstraints : ∀ row ∈ workers.split.rows, FlatOperation.ConstraintsHoldFlat
    (Verification.environment row.assignment) row.constraints
  /-- Standard row selectors are Boolean. -/
  standardSelectors : ∀ row ∈ workers.standard.rows, row.assignment row.columns.execute = 0 ∨ row.assignment row.columns.execute = 1
  /-- Split row selectors are Boolean. -/
  splitSelectors : ∀ row ∈ workers.split.rows, row.assignment row.columns.execute = 0 ∨ row.assignment row.columns.execute = 1

/-- Logical closure of the full unrolled layout under the native contribution mask.
    Inactive assignments need not stutter. Sampled scalar product equality is not a tuple permutation proof. -/
structure MaskedUnrolledAcceptance [Fact p.Prime] (trace : PooledTrace p) (workers : WorkerPools p)
    (program : List RVMachineProgramEntry) : Prop extends MaskedWorkersAccepted workers where
  /-- Every CPU assignment satisfies its imported constraints. -/
  constraints : ∀ row ∈ trace.rows, FlatOperation.ConstraintsHoldFlat
    (Verification.environment row.assignment) (row.constraints trace.rom)
  /-- The imported CPU execute selectors are Boolean. -/
  selectors : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 0 ∨ row.assignment row.columns.execute = 1
  /-- Public decoder membership applies to each participating CPU row. -/
  decoded : ∀ row ∈ (active trace).rows, Decoded (.pooled row.family) row.decoderQuery program
  /-- Full raw PC and clock tuples close before identity erasure. -/
  states : (some trace.initial :: contributions trace.rows (fun row => row.assignment row.columns.execute)
    (fun row => [row.finish])).Perm (some trace.terminal :: contributions trace.rows
      (fun row => row.assignment row.columns.execute) (fun row => [row.start]))
  /-- Masked virtual CSR tokens retain all caller and worker occurrences. -/
  requests : (maskedUnrolledRequests trace Requests.Request.issued ++ maskedWorkerRequests workers Requests.Request.empty).Perm
    (maskedUnrolledRequests trace Requests.Request.empty ++ maskedWorkerRequests workers Requests.Request.issued)
  /-- Masked architectural tokens share the public seed and terminal boundary. -/
  memory : (trace.initialMemory.map some ++ maskedUnrolledTokens trace Prod.snd ++ maskedWorkerTokens workers Prod.snd).Perm
    (trace.terminalMemory.map some ++ maskedUnrolledTokens trace Prod.fst ++ maskedWorkerTokens workers Prod.fst)

/-- Logical closure of the full unified layout under the same contribution mask. -/
structure MaskedUnifiedAcceptance [Fact p.Prime] (trace : UnifiedTrace p) (workers : WorkerPools p)
    (program : List RVMachineProgramEntry) : Prop extends MaskedWorkersAccepted workers where
  /-- Every CPU assignment satisfies its imported constraints. -/
  constraints : ∀ row ∈ trace.rows, FlatOperation.ConstraintsHoldFlat
    (Verification.environment row.assignment) (row.constraints trace.rom)
  /-- The imported CPU execute selectors are Boolean. -/
  selectors : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 0 ∨ row.assignment row.columns.execute = 1
  /-- Public decoder membership applies to each participating CPU row. -/
  decoded : ∀ row ∈ (active trace).rows, Decoded .unified row.decoderQuery program
  /-- Full raw PC and clock tuples close before identity erasure. -/
  states : (some trace.initial :: contributions trace.rows (fun row => row.assignment row.columns.execute)
    (fun row => [row.finish])).Perm (some trace.terminal :: contributions trace.rows
      (fun row => row.assignment row.columns.execute) (fun row => [row.start]))
  /-- Masked request tokens retain their full CSR and raw clocks. -/
  requests : (maskedUnifiedRequests trace Requests.Request.issued ++ maskedWorkerRequests workers Requests.Request.empty).Perm
    (maskedUnifiedRequests trace Requests.Request.empty ++ maskedWorkerRequests workers Requests.Request.issued)
  /-- Masked architectural tokens share the public seed and terminal boundary. -/
  memory : (trace.initialMemory.map some ++ maskedUnifiedTokens trace Prod.snd ++ maskedWorkerTokens workers Prod.snd).Perm
    (trace.terminalMemory.map some ++ maskedUnifiedTokens trace Prod.fst ++ maskedWorkerTokens workers Prod.fst)

/-- The UnrolledFullUnsigned target holds for the full masked layout and its participating CPU and worker rows. -/
def PaddedUnrolledFullUnsigned : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    BootInputs .unrolledFullUnsigned (active trace) initial cells program InitsTeardowns.importedLayout inits →
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) →
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NoSpecial5 program → NoMopR program →
    NonDeterminism.Pooled.StreamPorts (active trace) initial.input →
    MaskedUnrolledAcceptance trace workers program → RVRealizes trace initial cells


/-- The UnrolledReduced target holds for the full masked layout and its participating CPU and worker rows. -/
def PaddedUnrolledReduced : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    BootInputs .unrolledReduced (active trace) initial cells program InitsTeardowns.importedLayout inits →
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) →
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NonDeterminism.Pooled.StreamPorts (active trace) initial.input →
    MaskedUnrolledAcceptance trace workers program → RVRealizes trace initial cells


/-- The Unified target holds for the full masked layout and its participating CPU and worker rows. -/
def PaddedUnified : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)),
    BootInputs .unified (active trace) initial cells program InitsTeardowns.unifiedLayout inits →
    trace.rom = UnifiedReduced.Setup.tableRV initial →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NoSpecial5 program → UnifiedStreamPorts (active trace) initial.input →
    MaskedUnifiedAcceptance trace workers program → RVRealizes trace initial cells


end Airbender.Trace.Machine
