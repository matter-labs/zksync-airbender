import Airbender.Proofs.Bigint.NativeCall
import Airbender.Proofs.UnifiedReduced.StreamROMWorkerABI
import Airbender.Proofs.Blake2G.NativeCall
import Airbender.Proofs.Blake2Round.NativeCall

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
open ExternalBoundary.WorkerRAM
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- A word offset inside an aligned ABI stride cannot wrap below the RAM base. -/
theorem aligned_offset_ram (pointer : BitVec 32) (stride offset : Nat)
    (size : stride = 32 ∨ stride = 64 ∨ stride = 128)
    (aligned : pointer.toNat % stride = 0) (small : offset < stride)
    (outside : ROM.limit ≤ pointer.toNat) :
    ROM.limit ≤ (pointer + BitVec.ofNat 32 offset).toNat := by
  have bound := pointer.isLt
  have noWrap : pointer.toNat + offset < 2 ^ 32 := by
    rcases size with rfl | rfl | rfl <;> omega
  have offsetBound : offset < 2 ^ 32 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetBound,
    Nat.mod_eq_of_lt noWrap]
  omega

/-- Public cell locations and exact native codes give the worker-port domain. -/
theorem ports_domain_of_codes {p : Nat} {ports : Array MemoryPort}
    {cells : Vector Cell ports.size} {w : Nat → ZMod p}
    (codes : ∀ i : Fin ports.size, cells[i].addressCode = ports[i].address.code w)
    (locations : ∀ i : Fin ports.size, ∃ location : Location, location.cell = cells[i]) :
    ∀ port ∈ ports, ∃ location : Location, port.address.code w = location.cell.addressCode := by
  intro port member
  obtain ⟨i, bound, rfl⟩ := Array.mem_iff_getElem.mp member
  obtain ⟨location, same⟩ := locations ⟨i, bound⟩
  exact ⟨location, (codes ⟨i, bound⟩).symm.trans (congrArg Cell.addressCode same.symm)⟩

/-- The public bigint pointer contract bounds every word of its fixed footprint. -/
theorem bigint_cell_locations (pointers : Bigint.Addresses.Input)
    (outside : ROM.limit ≤ pointers.left.toBitVec.toNat ∧ ROM.limit ≤ pointers.right.toBitVec.toNat)
    (aligned : pointers.left.toBitVec.toNat % 32 = 0 ∧ pointers.right.toBitVec.toNat % 32 = 0) :
    ∀ i : Fin 19, ∃ location : Location, location.cell = (Bigint.Call.cells pointers)[i] := by
  intro i
  simp only [Bigint.Call.cells, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs with first left middle right
  · exact ⟨.register 10, rfl⟩
  · exact ⟨.ram _ (aligned_offset_ram _ 32 _ (Or.inl rfl) aligned.1 (by omega) outside.1), rfl⟩
  · exact ⟨.register 11, rfl⟩
  · exact ⟨.ram _ (aligned_offset_ram _ 32 _ (Or.inl rfl) aligned.2 (by omega) outside.2), rfl⟩
  · exact ⟨.register 12, rfl⟩

/-- The public extended-round pointers bound both complete memory blocks. -/
theorem round_cell_locations (input : Blake2Round.Row.Input)
    (outside : ROM.limit ≤ input.statePointer.toBitVec.toNat ∧ ROM.limit ≤ input.messagePointer.toBitVec.toNat)
    (aligned : input.statePointer.toBitVec.toNat % 128 = 0 ∧ input.messagePointer.toBitVec.toNat % 64 = 0) :
    ∀ i : Fin 43, ∃ location : Location, location.cell = (Blake2Round.Call.cells input)[i] := by
  intro i
  simp only [Blake2Round.Call.cells, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs with first state middle message
  · exact ⟨.register 10, rfl⟩
  · exact ⟨.ram _ (aligned_offset_ram _ 128 _ (Or.inr (Or.inr rfl)) aligned.1 (by omega) outside.1), rfl⟩
  · exact ⟨.register 11, rfl⟩
  · exact ⟨.ram _ (aligned_offset_ram _ 64 _ (Or.inr (Or.inl rfl)) aligned.2 (by omega) outside.2), rfl⟩
  · exact ⟨.register 12, rfl⟩

/-- The bounded G controller selects words inside its two public ABI blocks. -/
theorem g_cell_locations (input : Blake2G.Addresses.Input)
    (outside : ROM.limit ≤ input.statePointer.toBitVec.toNat ∧ ROM.limit ≤ input.messagePointer.toBitVec.toNat)
    (aligned : input.statePointer.toBitVec.toNat % 64 = 0 ∧ input.messagePointer.toBitVec.toNat % 64 = 0) :
    ∀ i : Fin 9, ∃ location : Location, location.cell = (Blake2G.Call.cells input)[i] := by
  have state (j : Fin 4) : ROM.limit ≤ (input.statePointer.toBitVec +
      BitVec.ofNat 32 (4 * (Blake2G.Control.step input.controller).stateOffsets[j])).toNat := by
    apply aligned_offset_ram _ 64 _ (Or.inr (Or.inl rfl)) aligned.1 _ outside.1
    have bounded := Blake2G.Control.Proofs.state_offsets_bounded input.controller j
    omega
  have message (j : Fin 2) : ROM.limit ≤ (input.messagePointer.toBitVec +
      BitVec.ofNat 32 (4 * (Blake2G.Control.step input.controller).messageOffsets[j])).toNat := by
    apply aligned_offset_ram _ 64 _ (Or.inr (Or.inl rfl)) aligned.2 _ outside.2
    have bounded := Blake2G.Control.Proofs.message_offsets_bounded input.controller j
    omega
  intro i
  fin_cases i
  · exact ⟨.register 10, rfl⟩
  · exact ⟨.ram _ (state 0), rfl⟩
  · exact ⟨.ram _ (state 1), rfl⟩
  · exact ⟨.ram _ (state 2), rfl⟩
  · exact ⟨.ram _ (state 3), rfl⟩
  · exact ⟨.register 11, rfl⟩
  · exact ⟨.ram _ (message 0), rfl⟩
  · exact ⟨.ram _ (message 1), rfl⟩
  · exact ⟨.register 12, rfl⟩

/-- Native bigint equations identify every port with its public ABI footprint. -/
theorem bigint_ports_domain {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable))
    (bounded : (Bigint.Addresses.nativeInput w).left.Bounded ∧
      (Bigint.Addresses.nativeInput w).right.Bounded)
    (outside : ROM.limit ≤ (Bigint.Addresses.nativeInput w).left.toBitVec.toNat ∧
      ROM.limit ≤ (Bigint.Addresses.nativeInput w).right.toBitVec.toNat)
    (aligned : (Bigint.Addresses.nativeInput w).left.toBitVec.toNat % 32 = 0 ∧
      (Bigint.Addresses.nativeInput w).right.toBitVec.toNat % 32 = 0)
    (observed : ∀ port ∈ Bigint.importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w) :
    ∀ port ∈ Bigint.importedConstraintsMemoryPorts, ∃ location : Location,
      port.address.code w = location.cell.addressCode := by
  let input := Bigint.Addresses.nativeInput w
  have mapping : Bigint.Addresses.Mapping input
      (Bigint.importedConstraintsIndirectPorts.map (fun port => port.address w)) w := by
    simp only [input, Caller.Proofs.bigint_native_input]
    exact ⟨rfl, rfl, rfl⟩
  have addresses := (Bigint.Addresses.Proofs.soundness (by decide) (by decide)
    input _ w ⟨bounded, core, mapping⟩).2.2
  exact ports_domain_of_codes (Bigint.Call.Proofs.cells_projection addresses observed)
    (bigint_cell_locations input outside aligned)

/-- Native G equations identify the controller-selected public footprint. -/
theorem g_ports_domain {w : Nat → ZMod babyBearModulus} (register : Fin 256)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)))
    (active : w 0 = 1)
    (control : (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word = ⟨register.val, 0⟩)
    (bounded : (Blake2G.Native.statePointer w).Bounded ∧ (Blake2G.Native.messagePointer w).Bounded)
    (outside : ROM.limit ≤ (Blake2G.Native.statePointer w).toBitVec.toNat ∧
      ROM.limit ≤ (Blake2G.Native.messagePointer w).toBitVec.toNat)
    (aligned : (Blake2G.Native.statePointer w).toBitVec.toNat % 64 = 0 ∧
      (Blake2G.Native.messagePointer w).toBitVec.toNat % 64 = 0)
    (observed : ∀ port ∈ Blake2G.importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w) :
    ∀ port ∈ Blake2G.importedConstraintsMemoryPorts, ∃ location : Location,
      port.address.code w = location.cell.addressCode := by
  let input : Blake2G.Addresses.Input := ⟨⟨register, true⟩,
    Blake2G.Native.statePointer w, Blake2G.Native.messagePointer w⟩
  have low := congrArg Word.lo ((Blake2G.Call.Proofs.controller_words w).1.symm.trans control)
  have mapping : Blake2G.Addresses.Mapping input
      (Blake2G.importedConstraintsIndirectPorts.map (fun port => port.address w)) w := by
    refine ⟨low.symm, active, ?_, ?_, rfl⟩
    all_goals simp [input, Blake2G.Native.statePointer, Blake2G.Native.messagePointer,
      Delegation.Row.readWord, Delegation.Row.ports, readToken, MemoryPort.readCode,
      MemoryToken.word, WordColumns.code, Blake2G.importedConstraintsMemoryPorts]
  have addresses := Blake2G.Addresses.Proofs.soundness (by decide) (by decide)
    input _ w ⟨bounded, core, mapping⟩
  exact ports_domain_of_codes (Blake2G.Call.Proofs.cells_projection addresses observed)
    (g_cell_locations input outside aligned)

/-- Native extended-round address equations need only bounded pointer words. -/
theorem round_ports_domain {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable))
    (bounded : (Blake2Round.Native.input 0 w).statePointer.Bounded ∧
      (Blake2Round.Native.input 0 w).messagePointer.Bounded)
    (outside : ROM.limit ≤ (Blake2Round.Native.input 0 w).statePointer.toBitVec.toNat ∧
      ROM.limit ≤ (Blake2Round.Native.input 0 w).messagePointer.toBitVec.toNat)
    (aligned : (Blake2Round.Native.input 0 w).statePointer.toBitVec.toNat % 128 = 0 ∧
      (Blake2Round.Native.input 0 w).messagePointer.toBitVec.toNat % 64 = 0)
    (observed : ∀ port ∈ Blake2Round.importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w) :
    ∀ port ∈ Blake2Round.importedConstraintsMemoryPorts, ∃ location : Location,
      port.address.code w = location.cell.addressCode := by
  let input := Blake2Round.Native.input 0 w
  have mapping := Blake2Round.Native.Proofs.native_mapping 0 core
  have addresses := Blake2Round.Addresses.Proofs.soundness (by decide) (by decide)
    ⟨input.statePointer, input.messagePointer⟩ (Blake2Round.Native.output w).addresses w
    ⟨bounded, core, mapping.statePointer, mapping.messagePointer, mapping.addresses⟩
  have native : Blake2Round.importedConstraintsIndirectPorts.map (fun port => port.address w) =
      Blake2Round.Addresses.expected ⟨input.statePointer, input.messagePointer⟩ :=
    mapping.addresses.symm.trans addresses
  exact ports_domain_of_codes (Blake2Round.Call.Proofs.cells_projection native observed)
    (round_cell_locations input outside aligned)

end Airbender.UnifiedReduced.Caller.Stream.Proofs
