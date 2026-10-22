import Airbender.Proofs.Keccak.NativeCall
import Airbender.Proofs.Keccak.CallExecution

namespace Airbender.Keccak.Call.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

theorem schedule_supported (i : Fin 649) : Supported (scheduleControl ⟨i.val, by omega⟩) := by
  by_cases last : 648 ≤ i.val
  · have same : i.val = 648 := by omega
    simp [Supported, scheduleControl, same]
  · constructor
    · change i.val / 27 ≤ 24
      omega
    · apply Or.inr
      change i.val / 27 < 24
      omega

theorem derived_control [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Keccak.Proofs.BoundaryCallInputs data initial domain)
    {row : Delegation.Row p} (member : row ∈ data.rows) :
    ∃ control : ControlState, Supported control ∧
      (readToken row.assignment importedConstraintsMemoryPorts[0]).word = ⟨control.packed, 0⟩ := by
  obtain ⟨ordered, count, permutation, _, controls⟩ := Keccak.Proofs.call_schedule hp accepted inputs
  obtain ⟨i, bound, same⟩ := List.mem_iff_getElem.mp (permutation.mem_iff.mpr member)
  have indexBound : i < 649 := by omega
  let index : Fin 649 := ⟨i, indexBound⟩
  have control := (controls index).1
  rw [same] at control
  refine ⟨scheduleControl ⟨i, by omega⟩, schedule_supported index, ?_⟩
  exact (controller_words row.assignment).1.trans control

theorem operation_inputs [Fact p.Prime]
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell}
    (inputs : Keccak.Proofs.BoundaryCallInputs data initial domain)
    (tables : data.setup = Delegation.modeledSetup Controller.rows) :
    Delegation.Proofs.BoundaryOperationInputs data initial domain Controller.rows := by
  refine ⟨inputs.memory, tables, ?_, ?_⟩
  · intro row member other
    have family := inputs.family row member
    rw [family] at other
    cases other
  · intro row member _
    exact inputs.active row member

theorem native_core [Fact p.Prime]
    {data : Delegation.MemoryData p}
    (accepted : Delegation.MemoryAccepted data)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    {w : Nat → ZMod p} (member : (⟨.keccak, w⟩ : Delegation.Row p) ∈ data.rows) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (setupTable Controller.rows)) := by
  have holds := accepted.constraints _ member
  simp only [Delegation.Row.constraints, tables, Delegation.modeledSetup] at holds
  exact Verification.holds_of_sublist holds
    (List.sublist_append_left (importedConstraints (setupTable Controller.rows)) importedConstraintsTimestampLookups)

theorem pointer_ram {w : Nat → ZMod p} (effects : Native.RowEffects w)
    (bounded : (statePointer w).Bounded)
    (access : ROM.limit ≤ (importedConstraintsIndirectPorts[0].address w).toNat) :
    ROM.limit ≤ (statePointer w).toBitVec.toNat ∧ (statePointer w).toBitVec.toNat % 256 = 0 := by
  have aligned : (statePointer w).toBitVec.toNat % 256 = 0 := by
    rw [Word.toBitVec_toNat bounded]
    simpa [statePointer, Word.value, limbBase, Nat.add_mod, Nat.mul_mod] using effects.addresses.aligned
  refine ⟨?_, aligned⟩
  by_contra outside
  have below : (statePointer w).toBitVec.toNat < ROM.limit := by omega
  have lane := effects.addresses.laneIndices 0
  change (w 7).val < 31 at lane
  have address := effects.addresses.addresses 0
  change importedConstraintsIndirectPorts[0].address w =
    (statePointer w).toBitVec + BitVec.ofNat 32 (8 * (w 7).val) at address
  rw [address] at access
  have offsetBound : 8 * (w 7).val < 2 ^ 32 := by norm_num; omega
  have sumBound : (statePointer w).toBitVec.toNat + 8 * (w 7).val < 2 ^ 32 := by
    norm_num [ROM.limit] at below ⊢
    omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetBound,
    Nat.mod_eq_of_lt sumBound] at access
  norm_num [ROM.limit] at below access
  omega

theorem abi_in_span [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Keccak.Proofs.BoundaryCallInputs data initial domain)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ data.rows) :
    ∃ control : ControlState, ABI (nativeArguments control row.assignment) ∧
      (readToken row.assignment importedConstraintsMemoryPorts[0]).word = ⟨control.packed, 0⟩ := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨control, supported, binding⟩ := derived_control clockBound accepted inputs member
  have memory : Keccak.Proofs.BoundaryMemoryInputs data initial domain Controller.rows :=
    ⟨inputs.memory, inputs.family, by rw [tables]; rfl, inputs.active⟩
  have bounds := Keccak.Memory.Proofs.value_bounds_at_boundary
    (by norm_num [timestampBase]; omega) accepted memory
  have family := inputs.family row member
  have active := inputs.active row member
  rcases row with ⟨kind, w⟩
  change kind = .keccak at family
  subst kind
  have core := native_core accepted tables member
  have readsBound : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded := by
    intro port present
    exact bounds.1 _ member port (by change port ∈ importedConstraintsMemoryPorts; exact present)
  have effects := Native.Proofs.native_effects hp inverse core active readsBound
  have pointerBound : (statePointer w).Bounded := by
    rw [← (pointer_words w).1]
    exact readsBound _ (Array.getElem_mem (by change 1 < 14; decide))
  have tracked := Delegation.Proofs.initialized_indirect_cell_at_boundary clockBound accepted inputs.memory
    (port := importedConstraintsMemoryPorts[2]) (indirect := importedConstraintsIndirectPorts[0])
    member (by change importedConstraintsMemoryPorts[2] ∈ importedConstraintsMemoryPorts
               exact Array.getElem_mem (by change 2 < 14; decide)) (indirect_shape 0)
  obtain ⟨pointerRAM, alignment⟩ := pointer_ram effects pointerBound (ram _ tracked)
  refine ⟨control, ⟨supported, pointerBound, pointerRAM, alignment, ?_⟩, binding⟩
  intro i
  simpa only [nativeArguments, Fin.getElem_fin, Vector.getElem_ofFn] using read_lane_bound readsBound i

end Airbender.Keccak.Call.Proofs
