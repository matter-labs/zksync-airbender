import Airbender.Proofs.Blake2G.WordFrame
import Airbender.Proofs.Blake2G.State
import Airbender.Proofs.Blake2G.NativeExecution
import Airbender.Proofs.Blake2Round.PhysicalWords

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

abbrev physicalWords (state : State) (pointer : BitVec 32) : Vector Word 16 :=
  Blake2Round.Proofs.blockWords state pointer 16 0

def stateLanes (controller : Control.Input) : Vector (Fin 16) 4 :=
  Vector.ofFn fun i => ⟨(Control.step controller).stateOffsets[i],
    Control.Proofs.state_offsets_bounded controller i⟩

def physicalInput (controller : Control.Input) (before : State) (state message : BitVec 32) :
    Blake2G.State.Input :=
  ⟨physicalWords before state, stateLanes controller,
    (physicalWords before message)[(Control.step controller).messageOffsets[0]]'(Control.Proofs.message_offsets_bounded controller 0),
    (physicalWords before message)[(Control.step controller).messageOffsets[1]]'(Control.Proofs.message_offsets_bounded controller 1)⟩

theorem native_encoded_words {p : Nat} {w : Nat → ZMod p} {before after : State}
    {state message : BitVec 32} (controller : Control.Input)
    (addresses : Addresses.spec ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after) (index : Fin 6) :
    let address := (Addresses.expected ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩)[index]
    ramEncoding before address = ((⟨.blakeG, w⟩ : Delegation.Row p).readWord (wordIndex index)) ∧
      ramEncoding after address = ((⟨.blakeG, w⟩ : Delegation.Row p).writtenWord (wordIndex index)) := by
  have member : wordPort index ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports :=
    Array.getElem_mem (wordIndex index).isLt
  have actual := indirect_word_observations (word_port_address index)
    (reads _ member) (writes _ member) (observed _ member)
  have address := congrArg (fun values : Vector (BitVec 32) 6 => values[index]) addresses
  simp only [Fin.getElem_fin, Vector.getElem_map] at address
  change importedConstraintsIndirectPorts[index].address w = _ at address
  rw [address] at actual
  exact ⟨ram_encoding_native (reads _ member) actual.1,
    ram_encoding_native (writes _ member) actual.2⟩

theorem physical_mixing_words {p : Nat} {w : Nat → ZMod p} {before after : State}
    {state message : BitVec 32} (controller : Control.Input)
    (observed : ∀ index : Fin 6,
      let address := (Addresses.expected ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩)[index]
      ramEncoding before address = ((⟨.blakeG, w⟩ : Delegation.Row p).readWord (wordIndex index)) ∧
        ramEncoding after address = ((⟨.blakeG, w⟩ : Delegation.Row p).writtenWord (wordIndex index))) :
    Blake2G.State.mixingInput (physicalInput controller before state message) = Native.input w ∧
      Blake2G.State.mixingOutput (physicalInput controller before state message)
        (physicalWords after state) = Native.output w := by
  have a := observed 0
  have b := observed 1
  have c := observed 2
  have d := observed 3
  have x := (observed 4).1
  have y := (observed 5).1
  simp [Addresses.expected, Word.ofBitVec_roundtrip] at a b c d x y
  constructor
  · simp only [Blake2G.State.mixingInput, physicalInput, stateLanes, physicalWords,
      Blake2Round.Proofs.blockWords, Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add]
    rw [a.1, b.1, c.1, d.1, x, y]
    rfl
  · simp only [Blake2G.State.mixingOutput, physicalInput, stateLanes, physicalWords,
      Blake2Round.Proofs.blockWords, Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add]
    rw [a.2, b.2, c.2, d.2]
    rfl

end Airbender.Blake2G.Proofs
