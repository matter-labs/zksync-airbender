import Airbender.Proofs.FullUnsigned.BootExecution
import Airbender.Proofs.FullUnsigned.SplitArgumentsAtCut

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open UnifiedReduced.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Complete native boot execution uses only derived worker input facts.
The shared history recovers split arguments at each actual selected caller.
No per-cut argument, instruction result or worker output is a premise. -/
theorem unrolled_full_boot_execution_of_native_inputs
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle) (splitBundles : List Keccak.Split.Bundle)
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus} {cells : List Cell}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (boot : PooledBootInputs trace initial cells
      (NativeDecoder.ProgramRows.programOf .fullUnsigned initial text) AddSub.Modular.External.decoderFields)
    (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (workerFamilies : ∀ worker ∈ workers.rows, FullUnsigned.standardCall worker.family)
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (control : Keccak.Split.Native.ControlSetupFacts splitWorkers.setup)
    (fixedEquations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached Keccak.Split.Native.Proofs.fixedSetup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (standard : ∀ worker ∈ workers.rows, SupportedWorker worker ∧
      ∀ port ∈ worker.ports, ∃ location : ExternalBoundary.WorkerRAM.Location,
        port.address.code worker.assignment = location.cell.addressCode)
    (split : ∀ worker ∈ splitWorkers.rows,
      Keccak.Split.Native.Proofs.nativeCallArguments splitWorkers.cached worker ∧
        ∀ port ∈ worker.ports splitWorkers.cached, ∃ location : ExternalBoundary.WorkerRAM.Location,
          port.address.code worker.assignment = location.cell.addressCode)
    (stream : List (BitVec 32)) (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    FullUnsigned.Realizes stream (FullUnsigned.Program.ofText initial text bundles splitBundles)
      trace initial cells (ROMView.token initial) ∧
      ∀ token ∈ trace.terminalMemory, (ROMView.token initial token).word.Bounded := by
  have ram : ExternalBoundary.WorkerRAM.Binding workers.rows := fun worker member => (standard worker member).2
  have splitRAM : ∀ edge ∈ splitWorkers.steps, ¬ ROMView.shadow edge.1.address := by
    intro edge member
    obtain ⟨worker, present, native⟩ := List.mem_flatMap.mp member
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp native
    obtain ⟨location, address⟩ := (split worker present).2 port (by simpa using included)
    change ¬ ROMView.shadow (port.address.code worker.assignment)
    rw [address]
    exact ExternalBoundary.WorkerRAM.Proofs.location_not_shadow location
  have commands : ∀ worker ∈ workers.rows, worker.family = .bigint →
      ∃ command, ExternalBoundary.BigintABI.Binding worker.assignment command := by
    intro worker member family
    simpa only [SupportedWorker, family] using (standard worker member).1
  have controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers.rows →
      ExternalBoundary.HashABI.RoundControl w := fun w member => (standard ⟨.blakeRound, w⟩ member).1
  have initialPC : trace.initial.word.lo < limbBase := by
    rw [boot.initialBoundary]
    change 0 < limbBase
    decide
  have clocks := ROMView.native_clocks (by decide) boot.seed boot.initialBoundary
  have seedClocks : ∀ token ∈ trace.initialMemory, (timeOfPair token.time).Bounded := by
    intro token member
    rw [boot.seed] at member
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp member
    simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]
  have nativeFacts := unrolled_full_memory_facts accepted equations active control clocks.initial clocks.aligned seedClocks
  have physical := PooledROMView.execution_boundary (by decide) boot
  have physicalAccepted := unrolled_full_rom_acceptance setup lookup accepted excluded initialPC
    nativeFacts boot.seed ram splitRAM
  have physicalLookup := unrolled_full_rom_lookup initial lookup
  have initialized : Transfer.Inputs
      (unrolledFullMemoryData (PooledROMView.data initial trace) workers splitWorkers) initial cells :=
    ⟨physical.image, boot.distinct.map cell_address_injective⟩
  apply unrolled_full_boot_execution_and_bounds_of_selected_inputs bundles splitBundles setup lookup accepted excluded boot
    workerSetup workerFamilies equations control fixedEquations active ram splitRAM commands controls ?_ stream ports
  intro events finalState permutation ordered history row member family selected worker present matched before givenPast
  exact unrolled_full_split_arguments_at_cut setup physicalLookup physicalAccepted excluded initialPC equations active
    clocks.initial clocks.aligned initialized.toNativeInputs boot.aligned row member family selected worker present matched
    (split worker present).1 permutation ordered history before givenPast

end Airbender.Compiler.MachineTargets.Proofs
