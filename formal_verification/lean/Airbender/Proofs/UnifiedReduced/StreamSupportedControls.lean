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
theorem supported_worker_of_reference [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {program : DelegationUse.Program} {initial state : State}
    (stream : List (BitVec 32)) (position : Nat)
    (valid : Stream.ValidDelegationUse program initial)
    (reachable : Stream.Reachable stream program initial (state, position))
    {entry : Delegation.Caller.ProgramEntry} (registered : entry ∈ program.callers)
    (pc : DelegationUse.AtPC state entry.pc)
    {worker : Delegation.Row babyBearModulus} (family : worker.family = entry.data.family)
    (bounds : ∀ port ∈ worker.ports, (readToken worker.assignment port).word.Bounded)
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read state = .ok (readToken worker.assignment port).word.toBitVec state) :
    SupportedWorker worker := by
  obtain ⟨bundle, bundled, index, codePosition, kind⟩ := valid.shapes.coverage entry registered
  obtain ⟨left, right, control, readLeft, readRight, readControl, pointers, controller⟩ :=
    valid.arguments stream (state, position) reachable bundle bundled index (codePosition ▸ pc)
  have actual {port : MemoryPort} (present : port ∈ worker.ports) {index : BitVec 5}
      (address : port.address.code worker.assignment = (Cell.register index).addressCode) :
      DelegationUse.ReadRegister state index (readToken worker.assignment port).word.toBitVec := by
    obtain ⟨cell, code, read⟩ := observed port present
    have same := cell_address_injective (code.trans address)
    rw [same] at read
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
      refine ⟨command, ?_⟩
      apply word_eq_of_bits (bounds _ (Array.getElem_mem (by change 18 < 19; decide))) (bigint_command_word_bounded command)
      exact (read_eq (actual (Array.getElem_mem (by change 18 < 19; decide)) rfl) readControl).trans commandValue
    | g reduced =>
      have same : native = .blakeG := by simpa only [shape, DelegationUse.Kind.family] using family
      subst native
      have indexBound : index.val < Blake2G.callCount reduced := by
        simpa only [shape, DelegationUse.Kind.calls] using index.isLt
      have controlValue : control = (Blake2G.controlAt reduced index.val).toBitVec := by
        simpa only [DelegationUse.ControlAt, shape] using controller
      have expected : (Blake2G.controlAt reduced index.val).Bounded := by
        cases reduced <;> simp [Blake2G.controlAt, Blake2G.callCount, Word.Bounded, limbBase] at indexBound ⊢ <;> omega
      refine ⟨⟨reduced, ⟨index.val, indexBound⟩, ?_⟩, ?_⟩
      · apply word_eq_of_bits (bounds _ (Array.getElem_mem (by change 8 < 9; decide))) expected
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
      refine ⟨flags, ⟨index.val, ten⟩, allowed, ?_⟩
      apply word_eq_of_bits (bounds _ (Array.getElem_mem (by change 42 < 43; decide))) expected
      exact (read_eq (actual (Array.getElem_mem (by change 42 < 43; decide)) rfl) readControl).trans controlValue

end Airbender.UnifiedReduced.Caller.Stream.Proofs
