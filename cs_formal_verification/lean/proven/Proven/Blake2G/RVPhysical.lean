module
public import Proven.Blake2G.RVStateTrace
public import Proven.Delegation.RVNativeViews
public import Proven.Blake2G.PhysicalWords
public import Proven.Defs.Circuits.Blake2G.Artifact
public import Proven.Defs.Circuits.Blake2G.State
public import Proven.Defs.Circuits.Blake2G.Control
public import Proven.Defs.Circuits.Blake2G.Controller
public import Proven.Defs.Circuits.Blake2G.Addresses

@[expose] public section

/-! RV twins of `PhysicalWords.lean`, `WordFrame.lean`, `PhysicalStep.lean` and `CallPhysical.lean`: each G call
    updates the actual RV work vector by the original Clean G and keeps the message block. RAM words are
    `rvRamEncoding` (RAM at any address, the shadow RAM below `ROM_END` included). -/

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

abbrev rvPhysicalWords (state : RV.State) (pointer : BitVec 32) : Vector Word 16 :=
  rvBlockWords state pointer 16 0

def rvPhysicalInput (controller : Control.Input) (before : RV.State) (state message : BitVec 32) :
    Blake2G.State.Input :=
  ⟨rvPhysicalWords before state, stateLanes controller,
    (rvPhysicalWords before message)[(Control.step controller).messageOffsets[0]]'(Control.Proofs.message_offsets_bounded controller 0),
    (rvPhysicalWords before message)[(Control.step controller).messageOffsets[1]]'(Control.Proofs.message_offsets_bounded controller 1)⟩

theorem rv_native_encoded_words {p : Nat} {w : Nat → ZMod p} {before after : RV.State}
    {state message : BitVec 32} (controller : Control.Input)
    (addresses : Addresses.spec ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w))) (index : Fin 6) :
    let address := (Addresses.expected ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩)[index]
    rvRamEncoding before address = ((⟨.blakeG, w⟩ : Delegation.Row p).readWord (wordIndex index)) ∧
      rvRamEncoding after address = ((⟨.blakeG, w⟩ : Delegation.Row p).writtenWord (wordIndex index)) := by
  have member : wordPort index ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports :=
    Array.getElem_mem (wordIndex index).isLt
  have actual := rv_indirect_word_observations (word_port_address index)
    (reads _ member) (writes _ member) (observed _ member)
  have address := congrArg (fun values : Vector (BitVec 32) 6 => values[index]) addresses
  simp only [Fin.getElem_fin, Vector.getElem_map] at address
  change importedConstraintsIndirectPorts[index].address w = _ at address
  rw [address] at actual
  exact actual

theorem rv_physical_mixing_words {p : Nat} {w : Nat → ZMod p} {before after : RV.State}
    {state message : BitVec 32} (controller : Control.Input)
    (observed : ∀ index : Fin 6,
      let address := (Addresses.expected ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩)[index]
      rvRamEncoding before address = ((⟨.blakeG, w⟩ : Delegation.Row p).readWord (wordIndex index)) ∧
        rvRamEncoding after address = ((⟨.blakeG, w⟩ : Delegation.Row p).writtenWord (wordIndex index))) :
    Blake2G.State.mixingInput (rvPhysicalInput controller before state message) = Native.input w ∧
      Blake2G.State.mixingOutput (rvPhysicalInput controller before state message)
        (rvPhysicalWords after state) = Native.output w := by
  have a := observed 0
  have b := observed 1
  have c := observed 2
  have d := observed 3
  have x := (observed 4).1
  have y := (observed 5).1
  simp [Addresses.expected, Word.ofBitVec_roundtrip] at a b c d x y
  constructor
  · simp only [Blake2G.State.mixingInput, rvPhysicalInput, stateLanes, rvPhysicalWords,
      rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add]
    rw [a.1, b.1, c.1, d.1, x, y]
    rfl
  · simp only [Blake2G.State.mixingOutput, rvPhysicalInput, stateLanes, rvPhysicalWords,
      rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add]
    rw [a.2, b.2, c.2, d.2]
    rfl

theorem rv_native_block_frame_if {p : Nat} {w : Nat → ZMod p}
    {state message : BitVec 32} {before after : RV.State} {cells : List Cell} {events : List MemoryAccess}
    (controller : Control.Input)
    (addresses : Addresses.spec ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (block : Bool) (distinct : block = false → state ≠ message)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeG w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (word : Fin 16)
    (untouched : block = true → ∀ lane : Fin 4,
      (Control.step controller).stateOffsets[lane] ≠ word.val) :
    rvRamEncoding after ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) =
      rvRamEncoding before ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) := by
  let target := Cell.ram ((if block then state else message) + BitVec.ofNat 32 (4 * word.val))
  have targetAligned : target.Aligned := by
    change ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)).toNat % 4 = 0
    have bound := word.isLt
    have base : (if block then state else message).toNat % 64 = 0 := by cases block <;> assumption
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have stateAbsent (lane : Fin 4) :
      (MemoryAddress.indirect importedConstraintsIndirectPorts[lane.val]).code w ≠ target.addressCode := by
    intro same
    have cell := indirect_cell same.symm
    have address := Cell.ram.inj cell
    have actual := congrArg (fun values : Vector (BitVec 32) 6 => values[lane.val]) addresses
    simp only [Vector.getElem_map] at actual
    have expected : (Addresses.expected ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩)[lane.val] =
      state + BitVec.ofNat 32 (4 * (Control.step controller).stateOffsets[lane]) := by
      fin_cases lane <;> simp [Addresses.expected, Word.ofBitVec_roundtrip]
    rw [expected] at actual
    change ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) =
      importedConstraintsIndirectPorts[lane.val].address w at address
    rw [actual] at address
    let selected : Fin 16 := ⟨(Control.step controller).stateOffsets[lane],
      Control.Proofs.state_offsets_bounded controller lane⟩
    cases block with
    | false =>
      exact aligned_block_words_distinct state message stateAligned messageAligned (distinct rfl) selected word address.symm
    | true =>
      have equal := block_word_injective state word selected address
      exact untouched rfl lane (congrArg Fin.val equal).symm
  have copies : ∀ event ∈ events, event.2.1 = target.addressCode →
      memoryWord event.2.2.1 = memoryWord event.2.2.2 := by
    intro event present same
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp present)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
    have indexed : ∃ i : Fin 9, port = importedConstraintsMemoryPorts[i.val] := by
      have member : port ∈ importedConstraintsMemoryPorts := by
        simpa only [Delegation.Row.ports, Array.mem_toList_iff] using portMember
      obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
      change i < 9 at bound
      exact ⟨⟨i, bound⟩, equal.symm⟩
    obtain ⟨i, rfl⟩ := indexed
    change importedConstraintsMemoryPorts[i.val].address.code w = target.addressCode at same
    fin_cases i
    · rfl
    · exact False.elim (stateAbsent 0 same)
    · exact False.elim (stateAbsent 1 same)
    · exact False.elim (stateAbsent 2 same)
    · exact False.elim (stateAbsent 3 same)
    · rfl
    · rfl
    · rfl
    · simp [importedConstraintsMemoryPorts, MemoryAddress.code, target, Cell.addressCode,
        Nat.pair_eq_pair] at same
  have read := rv_encoded_read (state := before) targetAligned
  have written := rv_history_cell_copy_frame history aligned target targetAligned copies read
  rw [rv_ram_encoding_read written]
  exact word_of_toBitVec (Word.ofBitVec_bound _)

theorem rv_native_block_frame {p : Nat} {w : Nat → ZMod p}
    {state message : BitVec 32} {before after : RV.State} {cells : List Cell} {events : List MemoryAccess}
    (controller : Control.Input)
    (addresses : Addresses.spec ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (distinct : state ≠ message)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeG w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (block : Bool) (word : Fin 16)
    (untouched : block = true → ∀ lane : Fin 4,
      (Control.step controller).stateOffsets[lane] ≠ word.val) :
    rvRamEncoding after ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) =
      rvRamEncoding before ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) := by
  exact rv_native_block_frame_if controller addresses stateAligned messageAligned block
    (fun _ => distinct) history permutation aligned word untouched

theorem rv_physical_state_result [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p} {state message : BitVec 32} {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w Variables.execute = 1) (controlBound : (w Variables.controlReadLo).val < 256)
    (addresses : Addresses.spec
      ⟨⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩,
        Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w)))
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeG w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    let controller : Control.Input := ⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩
    Blake2G.State.spec (rvPhysicalInput controller before state message) (rvPhysicalWords after state) := by
  let controller : Control.Input := ⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩
  have encoded := rv_native_encoded_words controller addresses reads writes observed
  obtain ⟨inputWords, outputWords⟩ := rv_physical_mixing_words controller encoded
  let input := rvPhysicalInput controller before state message
  let output := rvPhysicalWords after state
  have mapping : Blake2G.State.Mapping input output w := by
    constructor
    · change WordMapping (Blake2G.State.mixingInput (rvPhysicalInput controller before state message))
        (Blake2G.State.mixingOutput (rvPhysicalInput controller before state message) (rvPhysicalWords after state)) w
      rw [inputWords, outputWords]
      exact Native.Proofs.native_mapping w
    · intro index
      let controlOutput : Control.Output :=
        ⟨⟨(w Variables.controlWriteLo).val, (w Variables.controlWriteHi).val⟩,
          Variables.stateOffsetColumns.map (fun column => (w column).val),
          Variables.messageOffsetColumns.map (fun column => (w column).val)⟩
      have controlMapping : Control.Mapping controller controlOutput w := ⟨rfl, active, rfl⟩
      have enforced := Control.Proofs.soundness (by omega) controller controlOutput w ⟨core, controlMapping⟩
      have equal := congrArg (fun value : Control.Output => value.stateOffsets[index]) enforced
      fin_cases index <;> simpa [input, rvPhysicalInput, stateLanes, controlOutput] using equal
  have frame (word : Fin 16)
      (untouched : ∀ lane : Fin 4,
        (Control.step controller).stateOffsets[lane] ≠ word.val) :=
    rv_native_block_frame_if controller addresses stateAligned messageAligned true
      (fun impossible => by cases impossible) history permutation aligned word (fun _ => untouched)
  have interfaces : Blake2G.State.InterfaceAssumptions input output w := by
    refine ⟨active, controlBound, ?_, ?_⟩
    · constructor
      all_goals simp only [input, rvPhysicalInput, Blake2G.State.mixingInput, stateLanes,
        rvPhysicalWords, rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, rvRamEncoding]
      all_goals exact Word.ofBitVec_bound _
    · intro word untouched
      have absent : ∀ lane : Fin 4, (Control.step controller).stateOffsets[lane] ≠ word.val := by
        intro lane equal
        apply untouched lane
        apply Fin.ext
        simpa [input, rvPhysicalInput, stateLanes] using equal.symm
      simpa [input, output, rvPhysicalInput, rvPhysicalWords, rvBlockWords] using
        frame word absent
  exact Blake2G.State.Proofs.soundness (by omega) inverse input output w ⟨interfaces, core, mapping⟩

theorem rv_physical_state_step [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p} {state message : BitVec 32} {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w Variables.execute = 1) (controlBound : (w Variables.controlReadLo).val < 256)
    (addresses : Addresses.spec
      ⟨⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩,
        Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w)))
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (distinct : state ≠ message)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeG w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    let controller : Control.Input := ⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩
    Blake2G.State.spec (rvPhysicalInput controller before state message) (rvPhysicalWords after state) ∧
      rvPhysicalWords after message = rvPhysicalWords before message := by
  refine ⟨rv_physical_state_result hp inverse core active controlBound addresses reads writes observed
    stateAligned messageAligned history permutation aligned, ?_⟩
  apply Vector.ext
  intro i bound
  simpa [rvPhysicalWords, rvBlockWords] using
    rv_native_block_frame _ addresses stateAligned messageAligned distinct history permutation
      aligned false ⟨i, bound⟩ (fun equal => by cases equal)

end Airbender.Blake2G.Proofs
