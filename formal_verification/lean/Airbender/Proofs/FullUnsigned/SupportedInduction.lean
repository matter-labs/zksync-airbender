import Airbender.Proofs.FullUnsigned.NativeInputExecution
import Airbender.Proofs.FullUnsigned.PrefixBoot

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open UnifiedReduced.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem split_register_token_unchanged (initial : State) (cached : Bool)
    (worker : Keccak.Split.Native.Row babyBearModulus) (index : Fin 2) :
    ROMView.token initial (readToken worker.assignment (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker index)) =
      readToken worker.assignment (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker index) := by
  have outside : ¬ ROMView.shadow
      (readToken worker.assignment (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker index)).address := by
    change ¬ ROMView.shadow ((Keccak.Split.Native.Proofs.nativeRegisterPort cached worker index).address.code worker.assignment)
    rw [Keccak.Split.Native.Proofs.native_register_port_address]
    simp [MemoryAddress.code, ROMView.shadow]
  simp only [ROMView.token, outside, if_false]

variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Native prefix induction derives all standard and split input facts from
public full-reference supported use. No native command, controller, pointer,
port domain, instruction result or completed reference trace is assumed. -/
theorem unrolled_full_supported_native_inputs
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
    (valid : FullUnsigned.ValidDelegationUse (FullUnsigned.Program.ofText initial text bundles splitBundles) initial)
    (stream : List (BitVec 32)) (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    (∀ worker ∈ workers.rows, SupportedWorker worker ∧
      ∀ port ∈ worker.ports, ∃ location : ExternalBoundary.WorkerRAM.Location,
        port.address.code worker.assignment = location.cell.addressCode) ∧
    (∀ worker ∈ splitWorkers.rows, Keccak.Split.Native.Proofs.nativeCallArguments splitWorkers.cached worker ∧
      ∀ port ∈ worker.ports splitWorkers.cached, ∃ location : ExternalBoundary.WorkerRAM.Location,
        port.address.code worker.assignment = location.cell.addressCode) := by
  classical
  let program := FullUnsigned.Program.ofText initial text bundles splitBundles
  let standardGood := fun worker : Delegation.Row babyBearModulus => SupportedWorker worker ∧
    ∀ port ∈ worker.ports, ∃ location : ExternalBoundary.WorkerRAM.Location,
      port.address.code worker.assignment = location.cell.addressCode
  let splitGood := fun worker : Keccak.Split.Native.Row babyBearModulus =>
    Keccak.Split.Native.Proofs.nativeCallArguments splitWorkers.cached worker ∧
      ∀ port ∈ worker.ports splitWorkers.cached, ∃ location : ExternalBoundary.WorkerRAM.Location,
        port.address.code worker.assignment = location.cell.addressCode
  have initialPC : trace.initial.word.lo < limbBase := by
    rw [boot.initialBoundary]
    change 0 < limbBase
    decide
  have clocks := ROMView.native_clocks (by decide) boot.seed boot.initialBoundary
  have rowClocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states clocks.initial clocks.aligned
  have intervals := state_clock_interval (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states clocks.initial clocks.aligned
  have seedClocks : ∀ token ∈ trace.initialMemory, (timeOfPair token.time).Bounded := by
    intro token member
    rw [boot.seed] at member
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp member
    simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]
  have facts := unrolled_full_memory_facts accepted equations active control clocks.initial clocks.aligned seedClocks
  have initialPositive : 0 < (timeOfPair trace.initial.timestamp).value := by
    rw [boot.initialBoundary]
    change 0 < (4 : ZMod babyBearModulus).val + timestampBase * (0 : ZMod babyBearModulus).val
    rw [show (4 : ZMod babyBearModulus).val = 4 from ZMod.val_natCast_of_lt (by decide : 4 < babyBearModulus)]
    simp
  have next : ∀ clock, ∀ caller ∈ trace.rows, caller.family = .addSub →
      Delegation.Requests.Selected caller.assignment → caller.clock = clock →
      (∀ worker ∈ workers.rows, Delegation.Requests.fulfillment worker = Delegation.Requests.caller caller.assignment → standardGood worker) ∧
      (∀ worker ∈ splitWorkers.rows, worker.fulfillment splitWorkers.cached = Delegation.Requests.caller caller.assignment → splitGood worker) := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro caller called family selected current
      have floor := (intervals caller called).1
      change (timeOfPair trace.initial.timestamp).value ≤ caller.clock at floor
      have positive : 0 < caller.clock := by omega
      obtain ⟨memory, prefixAccepted, suffix⟩ := unrolled_full_prefix_accepted accepted equations active
        clocks.initial clocks.aligned facts called positive
      let prefixTrace := unrolledFullPrefixTrace trace caller.start memory
      let prefixWorkers := unrolledFullPrefixWorkers workers caller.start
      let prefixSplit := unrolledFullPrefixSplitWorkers splitWorkers caller.start
      have earlierStandard : ∀ worker ∈ prefixWorkers.rows, standardGood worker := by
        intro worker included
        have original := (List.mem_filter.mp included).1
        have boundary := of_decide_eq_true (List.mem_filter.mp included).2
        obtain ⟨other, present, otherFamily, otherSelected, matched, _, time⟩ :=
          unrolled_full_fulfillment_slot accepted equations active clocks.initial clocks.aligned
            (Delegation.Requests.fulfillment worker)
            (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨worker, original, rfl⟩)))
        change (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 3 ≤ caller.clock at boundary
        change (timeOfPair (Delegation.Requests.fulfillment worker).time).value = other.clock + 1 at time
        have less : other.clock < clock := by omega
        exact (ih other.clock less other present otherFamily otherSelected rfl).1 worker original matched
      have earlierSplit : ∀ worker ∈ prefixSplit.rows, splitGood worker := by
        intro worker included
        have original := (List.mem_filter.mp included).1
        have boundary := of_decide_eq_true (List.mem_filter.mp included).2
        obtain ⟨other, present, otherFamily, otherSelected, matched, _, time⟩ :=
          unrolled_full_fulfillment_slot accepted equations active clocks.initial clocks.aligned
            (worker.fulfillment splitWorkers.cached)
            (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨worker, original, rfl⟩)))
        change (timeOfPair (worker.fulfillment splitWorkers.cached).time).value + 3 ≤ caller.clock at boundary
        change (timeOfPair (worker.fulfillment splitWorkers.cached).time).value = other.clock + 1 at time
        have less : other.clock < clock := by omega
        exact (ih other.clock less other present otherFamily otherSelected rfl).2 worker original matched
      have prefixBoot := unrolled_full_prefix_boot setup lookup accepted excluded boot called prefixAccepted
      have prefixLookup : UnrolledDecoderExactLookup prefixTrace masks columns :=
        fun row member => lookup row (List.mem_of_mem_filter member)
      have prefixEquations : Keccak.Split.Native.EquationsHold prefixSplit.cached prefixSplit.setup prefixSplit.rows :=
        ⟨fun row member => equations.rowsHold row (List.mem_of_mem_filter member)⟩
      have prefixFixed : Keccak.Split.Native.EquationsHold prefixSplit.cached Keccak.Split.Native.Proofs.fixedSetup prefixSplit.rows :=
        ⟨fun row member => fixedEquations.rowsHold row (List.mem_of_mem_filter member)⟩
      have prefixActive : ∀ row ∈ prefixSplit.rows, row.assignment (row.columns prefixSplit.cached).execute = 1 :=
        fun row member => active row (List.mem_of_mem_filter member)
      have prefixFamilies : ∀ worker ∈ prefixWorkers.rows, FullUnsigned.standardCall worker.family :=
        fun worker member => workerFamilies worker (List.mem_of_mem_filter member)
      have prefixPorts : NonDeterminism.Pooled.StreamPorts prefixTrace stream :=
        ExternalStream.Proofs.ports_before Trace.Row.clock NonDeterminism.Pooled.isRead NonDeterminism.Pooled.response
          trace.rows (timeOfPair caller.start.timestamp).value ports
      obtain ⟨⟨state, execution, atPC, terminal⟩, terminalBounds⟩ :=
        unrolled_full_boot_execution_of_native_inputs bundles splitBundles setup prefixLookup prefixAccepted excluded prefixBoot
          workerSetup prefixFamilies prefixEquations control prefixFixed prefixActive earlierStandard earlierSplit stream prefixPorts
      have reachable : FullUnsigned.Reachable stream program initial (state, NonDeterminism.Pooled.readCount prefixTrace) := execution
      have requestTime : (timeOfPair (Delegation.Requests.caller caller.assignment).time).value = caller.clock + 1 := by
        have nativeClock := rowClocks caller called
        simp only [Trace.Row.columns, family, CircuitLayout.columns] at nativeClock
        have one : Delegation.Requests.callerPort.clock.offset = 1 := rfl
        simpa only [Delegation.Requests.caller, one, Trace.Row.clock, Trace.Row.columns,
          family, CircuitLayout.columns, decodeTimestamp, timeOfPair, rawPair] using
          (write_time (by decide) (base := rawPair caller.assignment AddSub.importedConstraintsTraceColumns.initialTime)
            nativeClock.1 nativeClock.2 (show 1 < 4 by decide)).2
      constructor
      · intro worker member matched
        have frontier : ∀ port ∈ worker.ports, readToken worker.assignment port ∈ memory := by
          intro port present
          let edge := (readToken worker.assignment port, worker.writeToken port)
          have native : edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps :=
            List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
              ⟨worker, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))))
          have stamp := unrolled_full_standard_event_clock accepted clocks.initial clocks.aligned member (edge := edge)
            (List.mem_map.mpr ⟨port, by simpa using present, rfl⟩)
          change (timeOfPair edge.2.time).value + 1 = (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 3 at stamp
          rw [matched, requestTime] at stamp
          exact unrolled_full_prefix_worker_read setup lookup accepted excluded initialPC equations active
            clocks.initial clocks.aligned facts caller called family selected positive suffix edge native (by omega)
            (Delegation.Proofs.port_not_zero worker present)
        obtain ⟨entry, included, _, entryPC, _, sameFamily⟩ := unrolled_full_standard_caller_source
          setup lookup accepted excluded initialPC caller called family selected worker matched
        have core := accepted.workerEquations worker member
        rw [workerSetup] at core
        apply unrolled_full_supported_standard_inputs stream (NonDeterminism.Pooled.readCount prefixTrace)
          valid reachable included (entryPC ▸ atPC) sameFamily core (accepted.workerActive worker member)
        · intro port present
          exact terminalBounds _ (frontier port present)
        · intro port present
          obtain ⟨cell, _, address, read⟩ := terminal _ (frontier port present)
          exact ⟨cell, address, read⟩
      · intro worker member matched
        have frontier : ∀ port ∈ worker.ports splitWorkers.cached, readToken worker.assignment port ∈ memory := by
          intro port present
          let edge := (readToken worker.assignment port, worker.writeToken splitWorkers.cached port)
          have native : edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps :=
            List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
              ⟨worker, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))
          have stamp := unrolled_full_split_event_clock accepted clocks.initial clocks.aligned member (edge := edge)
            (List.mem_map.mpr ⟨port, by simpa using present, rfl⟩)
          change (timeOfPair edge.2.time).value + 1 = (timeOfPair (worker.fulfillment splitWorkers.cached).time).value + 3 at stamp
          rw [matched, requestTime] at stamp
          exact unrolled_full_prefix_worker_read setup lookup accepted excluded initialPC equations active
            clocks.initial clocks.aligned facts caller called family selected positive suffix edge native (by omega)
            (Keccak.Split.Native.Proofs.port_not_zero splitWorkers.cached worker present)
        obtain ⟨entry, included, _, entryPC, _, sameKind⟩ := unrolled_full_split_caller_source
          setup lookup accepted excluded initialPC caller called family selected splitWorkers.cached worker matched
        apply unrolled_full_supported_split_native_inputs stream (NonDeterminism.Pooled.readCount prefixTrace)
          valid reachable included (entryPC ▸ atPC) splitWorkers.cached worker sameKind
          (fixedEquations.rowsHold worker member) (active worker member)
        · have bound := terminalBounds _ (frontier _ (Keccak.Split.Native.Proofs.native_register_port_mem splitWorkers.cached worker 1))
          simpa only [split_register_token_unchanged] using bound
        · intro register
          obtain ⟨cell, _, address, read⟩ := terminal _
            (frontier _ (Keccak.Split.Native.Proofs.native_register_port_mem splitWorkers.cached worker register))
          exact ⟨cell, address, by simpa only [split_register_token_unchanged] using read⟩
  constructor
  · intro worker member
    obtain ⟨caller, called, family, selected, matched, _⟩ := unrolled_full_standard_worker_slot
      accepted equations active clocks.initial clocks.aligned worker member
    exact (next caller.clock caller called family selected rfl).1 worker member matched
  · intro worker member
    obtain ⟨caller, called, family, selected, matched, _⟩ := unrolled_full_split_worker_slot
      accepted equations active clocks.initial clocks.aligned worker member
    exact (next caller.clock caller called family selected rfl).2 worker member matched

end Airbender.Compiler.MachineTargets.Proofs
