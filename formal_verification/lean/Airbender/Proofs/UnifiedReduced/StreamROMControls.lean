import Airbender.Proofs.UnifiedReduced.StreamWorkerDomains
import Airbender.Proofs.UnifiedReduced.SupportedUseControls
import Airbender.Review.Trace.UnifiedReduced.StreamCalls

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem word_eq_of_bits {one two : Word} (first : one.Bounded) (second : two.Bounded)
    (same : one.toBitVec = two.toBitVec) : one = two := by
  apply Word.eq_of_value first second
  simpa only [Word.toBitVec_toNat first, Word.toBitVec_toNat second] using congrArg BitVec.toNat same


/-- Public stream reachability transports wrapper arguments to native controls. -/
theorem supported_worker_and_ram_of_reference [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {program : DelegationUse.Program} {initial state : State}
    (stream : List (BitVec 32)) (position : Nat)
    (valid : Stream.ValidDelegationUse program initial)
    (reachable : Stream.Reachable stream program initial (state, position))
    {entry : Delegation.Caller.ProgramEntry} (registered : entry ∈ program.callers)
    (pc : DelegationUse.AtPC state entry.pc)
    {worker : Delegation.Row babyBearModulus} (family : worker.family = entry.data.family)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment worker.assignment)
      (worker.constraints (Delegation.modeledSetup Keccak.Controller.rows)))
    (active : worker.assignment worker.columns.execute = 1)
    (bounds : ∀ port ∈ worker.ports,
      (Trace.ROMView.token initial (readToken worker.assignment port)).word.Bounded)
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read state = .ok
          (Trace.ROMView.token initial (readToken worker.assignment port)).word.toBitVec state) :
    SupportedWorker worker ∧ ∀ port ∈ worker.ports,
      ∃ location : ExternalBoundary.WorkerRAM.Location,
        port.address.code worker.assignment = location.cell.addressCode := by
  obtain ⟨bundle, bundled, index, codePosition, kind⟩ := valid.shapes.coverage entry registered
  obtain ⟨left, right, control, readLeft, readRight, readControl, pointers, controller⟩ :=
    valid.arguments stream (state, position) reachable bundle bundled index (codePosition ▸ pc)
  have registerIdentity {port : MemoryPort} {index : BitVec 5}
      (address : port.address.code worker.assignment = (Cell.register index).addressCode) :
      Trace.ROMView.token initial (readToken worker.assignment port) =
        readToken worker.assignment port := by
    have outside : ¬ Trace.ROMView.shadow (readToken worker.assignment port).address := by
      change ¬ Trace.ROMView.shadow (port.address.code worker.assignment)
      rw [address]
      simp [Trace.ROMView.shadow, Cell.addressCode]
    simp [Trace.ROMView.token, outside]
  have actualBounds {port : MemoryPort} (present : port ∈ worker.ports) {index : BitVec 5}
      (address : port.address.code worker.assignment = (Cell.register index).addressCode) :
      (readToken worker.assignment port).word.Bounded := by
    simpa only [registerIdentity address] using bounds port present
  have located : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment := by
    intro port present
    obtain ⟨cell, code, _⟩ := observed port present
    exact ⟨cell, code⟩
  have actual {port : MemoryPort} (present : port ∈ worker.ports) {index : BitVec 5}
      (address : port.address.code worker.assignment = (Cell.register index).addressCode) :
      DelegationUse.ReadRegister state index (readToken worker.assignment port).word.toBitVec := by
    obtain ⟨cell, code, read⟩ := observed port present
    have same := cell_address_injective (code.trans address)
    rw [same, registerIdentity address] at read
    exact read
  have read_eq {index : BitVec 5} {one two : BitVec 32}
      (first : DelegationUse.ReadRegister state index one)
      (second : DelegationUse.ReadRegister state index two) : one = two :=
    (EStateM.Result.ok.inj (first.symm.trans second)).1
  have family : worker.family = bundle.kind.family := family.trans kind
  cases worker with
  | mk native w =>
    cases shape : bundle.kind with
    | bigint =>
      have same : native = .bigint := by simpa only [shape, DelegationUse.Kind.family] using family
      subst native
      obtain ⟨command, commandValue⟩ : ∃ command : ExternalBoundary.BigintABI.Command,
          control = command.word.toBitVec := by
        simpa only [DelegationUse.ControlAt, shape] using controller
      constructor
      · refine ⟨command, ?_⟩
        apply word_eq_of_bits (actualBounds (index := 12) (Array.getElem_mem (by change 18 < 19; decide)) rfl) (bigint_command_word_bounded command)
        exact (read_eq (actual (Array.getElem_mem (by change 18 < 19; decide)) rfl) readControl).trans commandValue
      · have leftValue : (Bigint.Addresses.nativeInput w).left.toBitVec = left :=
          read_eq (actual (Array.getElem_mem (by change 0 < 19; decide)) rfl) readLeft
        have rightValue : (Bigint.Addresses.nativeInput w).right.toBitVec = right :=
          read_eq (actual (Array.getElem_mem (by change 9 < 19; decide)) rfl) readRight
        have nativeCore := Verification.holds_of_sublist core
          (List.sublist_append_left (Bigint.importedConstraints Bigint.setupTable)
            Bigint.importedConstraintsTimestampLookups)
        apply bigint_ports_domain nativeCore
          ⟨actualBounds (index := 10) (Array.getElem_mem (by change 0 < 19; decide)) rfl,
            actualBounds (index := 11) (Array.getElem_mem (by change 9 < 19; decide)) rfl⟩
          (by simpa only [leftValue, rightValue] using And.intro pointers.1 pointers.2.1)
          (by simpa only [leftValue, rightValue, shape] using pointers.2.2.2)
          located
    | g reduced =>
      have same : native = .blakeG := by simpa only [shape, DelegationUse.Kind.family] using family
      subst native
      have indexBound : index.val < Blake2G.callCount reduced := by
        simpa only [shape, DelegationUse.Kind.calls] using index.isLt
      have controlValue : control = (Blake2G.controlAt reduced index.val).toBitVec := by
        simpa only [DelegationUse.ControlAt, shape] using controller
      have expected : (Blake2G.controlAt reduced index.val).Bounded := by
        cases reduced <;> simp [Blake2G.controlAt, Blake2G.callCount, Word.Bounded, limbBase] at indexBound ⊢ <;> omega
      constructor
      · refine ⟨⟨reduced, ⟨index.val, indexBound⟩, ?_⟩, ?_⟩
        · apply word_eq_of_bits (actualBounds (index := 12) (Array.getElem_mem (by change 8 < 9; decide)) rfl) expected
          exact (read_eq (actual (Array.getElem_mem (by change 8 < 9; decide)) rfl) readControl).trans controlValue
        · have different : left ≠ right := pointers.2.2.1
          have leftValue := read_eq (actual (port := Blake2G.importedConstraintsMemoryPorts[0])
            (Array.getElem_mem (by change 0 < 9; decide)) rfl) readLeft
          have rightValue := read_eq (actual (port := Blake2G.importedConstraintsMemoryPorts[5])
            (Array.getElem_mem (by change 5 < 9; decide)) rfl) readRight
          change (readToken w Blake2G.importedConstraintsMemoryPorts[0]).word.toBitVec ≠
            (readToken w Blake2G.importedConstraintsMemoryPorts[5]).word.toBitVec
          rw [leftValue, rightValue]
          exact different
      · have leftValue : (Blake2G.Native.statePointer w).toBitVec = left :=
          read_eq (actual (Array.getElem_mem (by change 0 < 9; decide)) rfl) readLeft
        have rightValue : (Blake2G.Native.messagePointer w).toBitVec = right :=
          read_eq (actual (Array.getElem_mem (by change 5 < 9; decide)) rfl) readRight
        have nativeCore := Verification.holds_of_sublist core
          (List.sublist_append_left
            (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows))
            Blake2G.importedConstraintsTimestampLookups)
        have binding : (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word =
            Blake2G.controlAt reduced index.val := by
          apply word_eq_of_bits
            (actualBounds (index := 12) (Array.getElem_mem (by change 8 < 9; decide)) rfl) expected
          exact (read_eq (actual (Array.getElem_mem (by change 8 < 9; decide)) rfl) readControl).trans controlValue
        apply g_ports_domain (Blake2G.controllerAt reduced index.val).register nativeCore active binding
          ⟨actualBounds (index := 10) (Array.getElem_mem (by change 0 < 9; decide)) rfl,
            actualBounds (index := 11) (Array.getElem_mem (by change 5 < 9; decide)) rfl⟩
          (by simpa only [leftValue, rightValue] using And.intro pointers.1 pointers.2.1)
          (by simpa only [leftValue, rightValue, shape] using pointers.2.2.2)
          located
    | round reduced =>
      have same : native = .blakeRound := by simpa only [shape, DelegationUse.Kind.family] using family
      subst native
      obtain ⟨flags, mode, controlValue⟩ : ∃ flags : Fin 8,
          (flags.val % 2 = 1 ↔ reduced = true) ∧
            control = (Blake2Round.controlAt flags index.val).toBitVec := by
        simpa only [DelegationUse.ControlAt, shape] using controller
      have indexBound : index.val < if reduced then 7 else 10 := by
        simpa only [shape, DelegationUse.Kind.calls] using index.isLt
      have ten : index.val < 10 := by split at indexBound <;> omega
      have allowed : index.val < if flags.val % 2 = 1 then 7 else 10 := by
        cases reduced <;> simp_all
      have expected : (Blake2Round.controlAt flags index.val).Bounded := by
        have pow : 2 ^ index.val % 1024 < 1024 := Nat.mod_lt _ (by decide)
        have flagBound := flags.isLt
        simp only [Blake2Round.controlAt, Word.Bounded, limbBase]
        omega
      constructor
      · refine ⟨flags, ⟨index.val, ten⟩, allowed, ?_⟩
        apply word_eq_of_bits (actualBounds (index := 12) (Array.getElem_mem (by change 42 < 43; decide)) rfl) expected
        exact (read_eq (actual (Array.getElem_mem (by change 42 < 43; decide)) rfl) readControl).trans controlValue
      · have leftValue : (Blake2Round.Native.input 0 w).statePointer.toBitVec = left :=
          read_eq (actual (Array.getElem_mem (by change 0 < 43; decide)) rfl) readLeft
        have rightValue : (Blake2Round.Native.input 0 w).messagePointer.toBitVec = right :=
          read_eq (actual (Array.getElem_mem (by change 25 < 43; decide)) rfl) readRight
        have nativeCore := Verification.holds_of_sublist core
          (List.sublist_append_left (Blake2Round.importedConstraints Blake2Round.setupTable)
            Blake2Round.importedConstraintsTimestampLookups)
        apply round_ports_domain nativeCore
          ⟨actualBounds (index := 10) (Array.getElem_mem (by change 0 < 43; decide)) rfl,
            actualBounds (index := 11) (Array.getElem_mem (by change 25 < 43; decide)) rfl⟩
          (by simpa only [leftValue, rightValue] using And.intro pointers.1 pointers.2.1)
          (by simpa only [leftValue, rightValue, shape] using pointers.2.2.2)
          located

end Airbender.UnifiedReduced.Caller.Stream.Proofs
