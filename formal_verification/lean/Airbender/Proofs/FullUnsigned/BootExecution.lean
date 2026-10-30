import Airbender.Proofs.FullUnsigned.NativeExecution
import Airbender.Proofs.FullUnsigned.NativeROM
import Airbender.Proofs.FullUnsigned.MemoryHistory
import Airbender.Proofs.Reduced.ROMInputs

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
open AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

private theorem full_round_masks
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (setup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers.rows →
      ExternalBoundary.HashABI.RoundControl w) :
    ∀ row ∈ workers.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  intro row member family
  rcases row with ⟨kind, w⟩
  cases family
  have core := accepted.workerEquations ⟨.blakeRound, w⟩ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2Round.clockConstraints workers.setup.blakeRound) at core
  rw [setup] at core
  have holds := Verification.holds_of_sublist core
    (List.sublist_append_left (Blake2Round.importedConstraints Blake2Round.setupTable)
      Blake2Round.importedConstraintsTimestampLookups)
  obtain ⟨flags, round, _, control⟩ := controls w member
  have powerBound : 2 ^ round.val < 1024 := by fin_cases round <;> decide
  have packed : (w 136).val = flags.val + 8 * 2 ^ round.val := by
    have high := congrArg Word.hi control
    simpa [read_word, Blake2Round.importedConstraintsMemoryPorts,
      WordColumns.evaluate, Blake2Round.controlAt, Nat.mod_eq_of_lt powerBound] using high
  exact ⟨round, (Blake2Round.Proofs.exclusive_mask_iff (by decide) holds round).mpr ⟨flags, packed⟩⟩

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Complete full execution starts from the native zero boot image and returns
its unchanged terminal interface through public ROM interpretation. Supported
worker input contracts and the formal fixed-setup bridge remain separate. -/
theorem unrolled_full_boot_execution_and_bounds
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
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (splitRAM : ∀ edge ∈ splitWorkers.steps, ¬ ROMView.shadow edge.1.address)
    (commands : ∀ worker ∈ workers.rows, worker.family = .bigint →
      ∃ command, ExternalBoundary.BigintABI.Binding worker.assignment command)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (splitInputs : ∀ events finalState,
      events.Perm ((unrolledFullMemoryData (PooledROMView.data initial trace) workers splitWorkers).steps.map transferEvent) →
      events.Pairwise (fun a b => b.1 ≤ a.1) → SailHistory cells events initial finalState →
      ∀ row ∈ (PooledROMView.data initial trace).rows, ∀ worker ∈ splitWorkers.rows,
        worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment →
        ∀ before, SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before →
          ∃ index : Fin 361, Keccak.Split.ArgumentsAt index.val before)
    (stream : List (BitVec 32)) (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    (FullUnsigned.Realizes stream (FullUnsigned.Program.ofText initial text bundles splitBundles)
      trace initial cells (ROMView.token initial)) ∧
      ∀ token ∈ trace.terminalMemory, (ROMView.token initial token).word.Bounded := by
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
  let physicalTrace := PooledROMView.data initial trace
  have physical := PooledROMView.execution_boundary (by decide) boot
  have physicalAccepted := unrolled_full_rom_acceptance setup lookup accepted excluded initialPC
    nativeFacts boot.seed ram splitRAM
  have physicalLookup := unrolled_full_rom_lookup initial lookup
  have physicalFacts := unrolled_full_memory_facts physicalAccepted equations active control
    clocks.initial clocks.aligned (image_clocks physical.image)
  have initialized : Transfer.Inputs (unrolledFullMemoryData physicalTrace workers splitWorkers) initial cells :=
    ⟨physical.image, boot.distinct.map cell_address_injective⟩
  have inputs := initialized.toNativeInputs
  have rounds := full_round_masks accepted workerSetup controls
  obtain ⟨bounds, terminalBounds, _, events, after, _, permutation, ordered, history, _, terminal⟩ :=
    unrolled_full_memory_history setup physicalLookup physicalAccepted excluded initialPC clocks.initial clocks.aligned
      physical.image physical.wordSetup physical.subwordSetup workerSetup rounds equations control fixedEquations active
      inputs boot.aligned
  have readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2 :=
    fun event member => unrolled_full_rom_unchanged setup lookup accepted excluded initialPC nativeFacts
      boot.seed ram splitRAM (permutation.mem_iff.mp member)
  have closure : VerifierBoundary.BootClosure physicalTrace.initial
      (physicalTrace.rows.map Row.start) (physicalTrace.rows.map Row.finish) := by
    simpa only [physicalTrace, PooledROMView.data, List.map_map, Function.comp_def,
      PooledROMView.row_start, PooledROMView.row_finish] using boot.verifierBoundary
  obtain ⟨stamp, initialBound⟩ := physical.initialPC
  have pc := initial_state_pc (by decide) initialBound
  have physicalPorts : NonDeterminism.Pooled.StreamPorts physicalTrace stream :=
    interpreted_stream_ports (data := ⟨trace, workers, []⟩) initial ports
  obtain ⟨finalState, execution, finalPC, sinks⟩ := unrolled_full_physical_execution bundles splitBundles
    setup physicalLookup physicalAccepted excluded initialPC closure equations fixedEquations active
    clocks.initial clocks.aligned physical.image physical.wordSetup physical.subwordSetup boot.aligned
    boot.toPooledPublicInputs permutation ordered history readonly physicalFacts inputs workerSetup workerFamilies
    bounds ram commands controls (splitInputs events after permutation ordered history) stream physicalPorts pc terminal
  have nativeBounds : ∀ token ∈ trace.terminalMemory, (ROMView.token initial token).word.Bounded := by
    intro token member
    exact terminalBounds _ (List.mem_map.mpr ⟨token, member, rfl⟩)
  refine ⟨?_, nativeBounds⟩
  refine ⟨finalState, ?_, finalPC, ?_⟩
  · have count : NonDeterminism.Pooled.readCount (PooledROMView.data initial trace) =
        NonDeterminism.Pooled.readCount trace :=
      interpreted_read_count initial (⟨trace, workers, []⟩ : Delegation.Caller.RequestTrace babyBearModulus)
    rw [count] at execution
    exact execution
  · intro token member
    obtain ⟨cell, included, address, read⟩ := sinks _ (List.mem_map.mpr ⟨token, member, rfl⟩)
    exact ⟨cell, included, by simpa only [ROMView.token_address] using address, read⟩


/-- The complete native zero-boot execution keeps its original terminal interface. -/
theorem unrolled_full_boot_execution
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
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (splitRAM : ∀ edge ∈ splitWorkers.steps, ¬ ROMView.shadow edge.1.address)
    (commands : ∀ worker ∈ workers.rows, worker.family = .bigint →
      ∃ command, ExternalBoundary.BigintABI.Binding worker.assignment command)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (splitInputs : ∀ events finalState,
      events.Perm ((unrolledFullMemoryData (PooledROMView.data initial trace) workers splitWorkers).steps.map transferEvent) →
      events.Pairwise (fun a b => b.1 ≤ a.1) → SailHistory cells events initial finalState →
      ∀ row ∈ (PooledROMView.data initial trace).rows, ∀ worker ∈ splitWorkers.rows,
        worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment →
        ∀ before, SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before →
          ∃ index : Fin 361, Keccak.Split.ArgumentsAt index.val before)
    (stream : List (BitVec 32)) (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    FullUnsigned.Realizes stream (FullUnsigned.Program.ofText initial text bundles splitBundles)
      trace initial cells (ROMView.token initial) := by
  exact (unrolled_full_boot_execution_and_bounds bundles splitBundles setup lookup accepted excluded boot
    workerSetup workerFamilies equations control fixedEquations active ram splitRAM commands controls
    splitInputs stream ports).1

end Airbender.Compiler.MachineTargets.Proofs
