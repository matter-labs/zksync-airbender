import Airbender.Review.Circuits.Bigint.PointerABI
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.Delegation.NativeViews
import Airbender.Proofs.Bigint.Addresses

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem worker_indirect_ram [Fact p.Prime]
    {data : RequestTrace p} {initial : State} {cells : List Cell}
    (effects : MixedMemoryEffects data initial cells)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    {port : MemoryPort} (present : port ∈ worker.ports)
    {indirect : Verification.IndirectPort} (shape : port.address = .indirect indirect) :
    ROM.limit ≤ (indirect.address worker.assignment).toNat := by
  obtain ⟨cell, tracked, code, _⟩ := effects.addresses _ (mixed_worker_member member present)
  change cell.addressCode = port.address.code worker.assignment at code
  rw [shape] at code
  have same := Delegation.Proofs.indirect_cell code
  exact ram _ (same ▸ tracked)

theorem bigint_native_input {p : Nat} (w : Nat → ZMod p) :
    Bigint.Addresses.nativeInput w = ⟨⟨(w 3).val, (w 4).val⟩, ⟨(w 37).val, (w 38).val⟩⟩ := by
  simp [Bigint.Addresses.nativeInput, Trace.Proofs.read_word,
    Bigint.importedConstraintsMemoryPorts, WordColumns.evaluate]

theorem bigint_base_codes {p : Nat} (w : Nat → ZMod p) :
    let addresses := (⟨.bigint, w⟩ : Delegation.Row p).memorySteps.map fun edge => edge.1.address
    addresses.get ⟨1, by change 1 < 19; decide⟩ =
      Nat.pair 1 (Nat.pair (Bigint.Addresses.nativeInput w).left.lo (Bigint.Addresses.nativeInput w).left.hi) ∧
    addresses.get ⟨10, by change 10 < 19; decide⟩ =
      Nat.pair 1 (Nat.pair (Bigint.Addresses.nativeInput w).right.lo (Bigint.Addresses.nativeInput w).right.hi) := by
  simp [Delegation.Row.memorySteps, Delegation.Row.ports, Bigint.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, bigint_native_input]

theorem bigint_pointer_ports :
    Bigint.importedConstraintsMemoryPorts[1].address = .indirect Bigint.importedConstraintsIndirectPorts[0] ∧
    Bigint.importedConstraintsMemoryPorts[10].address = .indirect Bigint.importedConstraintsIndirectPorts[8] := by
  decide +kernel

theorem bigint_pointer_abi
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat) :
    ∀ worker ∈ data.workers.rows, worker.family = .bigint →
      Bigint.Addresses.PointerABI (Bigint.Addresses.nativeInput worker.assignment) := by
  have effects := mixed_memory_effects accepted inputs
  intro worker member family
  rcases worker with ⟨kind, w⟩
  change kind = .bigint at family
  subst kind
  have reads (i : Fin 19) : (readToken w Bigint.importedConstraintsMemoryPorts[i]).word.Bounded :=
    (effects.words _ (mixed_worker_member member (by
      change Bigint.importedConstraintsMemoryPorts[i] ∈ Bigint.importedConstraintsMemoryPorts
      exact Array.getElem_mem i.isLt))).1
  have bounds : (Bigint.Addresses.nativeInput w).left.Bounded ∧
      (Bigint.Addresses.nativeInput w).right.Bounded := ⟨reads 0, reads 9⟩
  have holds := accepted.workerConstraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Bigint.clockConstraints data.workers.setup.bigint) at holds
  rw [inputs.tables] at holds
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Bigint.clockConstraints Bigint.setupTable) at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (Bigint.importedConstraints Bigint.setupTable) Bigint.importedConstraintsTimestampLookups)
  have alignment := Bigint.Addresses.Proofs.pointer_alignment (by decide) (by decide) core
  have aligned : (Bigint.Addresses.nativeInput w).left.lo % 32 = 0 ∧
      (Bigint.Addresses.nativeInput w).right.lo % 32 = 0 := by
    simpa only [bigint_native_input] using alignment
  refine ⟨bounds, ?_, ?_, ?_⟩
  · have left := worker_indirect_ram effects ram member (port := Bigint.importedConstraintsMemoryPorts[1])
      (indirect := Bigint.importedConstraintsIndirectPorts[0])
      (Array.getElem_mem (by change 1 < 19; decide)) bigint_pointer_ports.1
    have right := worker_indirect_ram effects ram member (port := Bigint.importedConstraintsMemoryPorts[10])
      (indirect := Bigint.importedConstraintsIndirectPorts[8])
      (Array.getElem_mem (by change 10 < 19; decide)) bigint_pointer_ports.2
    have both := And.intro left right
    simpa [Bigint.importedConstraintsIndirectPorts, Verification.IndirectPort.address, bigint_native_input] using both
  · rw [Word.toBitVec_toNat bounds.1, Word.toBitVec_toNat bounds.2]
    simpa [Word.value, limbBase, Nat.add_mod, Nat.mul_mod] using aligned
  · intro same
    have values := congrArg BitVec.toNat same
    rw [Word.toBitVec_toNat bounds.1, Word.toBitVec_toNat bounds.2] at values
    have words := Word.eq_of_value bounds.1 bounds.2 values
    have codes := congrArg (fun word : Word => Nat.pair 1 (Nat.pair word.lo word.hi)) words
    have roles := bigint_base_codes w
    rw [← roles.1, ← roles.2] at codes
    have unique := worker_addresses_distinct (by decide) (by decide) accepted inputs effects.requests member
    have indices := unique.get_inj_iff.mp codes
    have impossible := congrArg Fin.val indices
    norm_num at impossible

end Airbender.UnifiedReduced.Caller.Proofs
