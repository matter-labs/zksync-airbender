import Airbender.Proofs.UnifiedReduced.StreamMemory
import Airbender.Proofs.UnifiedReduced.WorkerABI

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Exact native matching separates the actual addresses of one worker. -/
theorem worker_addresses_distinct
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ data.workers.rows) :
    (worker.memorySteps.map fun edge => edge.1.address).Nodup := by
  have facts := mixed_memory_facts (by decide) (by decide) accepted
    inputs.publicProgram inputs.initialization effects.requests
  have initialized : Transfer.Inputs (mixedData data) initial cells :=
    ⟨inputs.initialization, inputs.distinct⟩
  have rawUnique := Transfer.raw_address_clocks_distinct facts initialized.toBoundaryInputs
  have nativeSub : (data.mixedSteps.map transferEvent).Sublist (Transfer.rawEvents (mixedData data)) :=
    List.sublist_append_right _ _
  have nativeUnique := rawUnique.sublist (nativeSub.map (fun event => (event.1, event.2.1)))
  have rowSub : worker.memorySteps.Sublist data.workers.steps := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Delegation.MemoryData.steps]
      using (List.singleton_sublist.mpr member).flatMap Delegation.Row.memorySteps
  have allSub : worker.memorySteps.Sublist data.mixedSteps :=
    rowSub.trans (List.sublist_append_right _ _)
  have unique := nativeUnique.sublist ((allSub.map transferEvent).map
    (fun event => (event.1, event.2.1)))
  have constant : (worker.memorySteps.map transferEvent).map (fun event => (event.1, event.2.1)) =
      (worker.memorySteps.map fun edge => edge.1.address).map
        (fun address => (workerClock worker, address)) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro edge present
    have time := worker_event_clock (by decide) effects.requests member
      (List.mem_map.mpr ⟨edge, present, rfl⟩)
    simpa only [transferEvent] using congrArg (fun clock => (clock, edge.1.address)) time
  rw [constant] at unique
  exact unique.of_map _

/-- Native memory and arithmetic derive the bigint pointer ABI. -/
theorem bigint_pointer_abi
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat) :
    ∀ worker ∈ data.workers.rows, worker.family = .bigint →
      Bigint.Addresses.PointerABI (Bigint.Addresses.nativeInput worker.assignment) := by
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
    have unique := worker_addresses_distinct accepted inputs effects member
    have indices := unique.get_inj_iff.mp codes
    have impossible := congrArg Fin.val indices
    norm_num at impossible

end Airbender.UnifiedReduced.Caller.Stream.Proofs
