import Airbender.Proofs.Blake2Round.StateTransport
import Airbender.Proofs.Blake2Round.Compression

namespace Airbender.Blake2Round.Proofs
open Trace Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def blockWords (state : State) (pointer : BitVec 32) (n offset : Nat) : Vector Word n :=
  Vector.ofFn fun i => ramEncoding state (pointer + BitVec.ofNat 32 (4 * (offset + i.val)))

def physicalState (state : State) (pointer : BitVec 32) : Compression.State :=
  (blockWords state pointer 8 0, blockWords state pointer 16 8)

theorem native_encoded_words {p : Nat} {w : Nat → ZMod p} {before after : State}
    {statePointer messagePointer : BitVec 32}
    (reads : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ index : Fin 40,
      let address := if index.val < 24 then statePointer + BitVec.ofNat 32 (4 * index.val)
        else messagePointer + BitVec.ofNat 32 (4 * (index.val - 24))
      ramWord before address = ((⟨.blakeRound, w⟩ : Delegation.Row p).readWord (wordIndex index)).value ∧
        ramWord after address = ((⟨.blakeRound, w⟩ : Delegation.Row p).writtenWord (wordIndex index)).value) :
    ∀ index : Fin 40,
      let address := if index.val < 24 then statePointer + BitVec.ofNat 32 (4 * index.val)
        else messagePointer + BitVec.ofNat 32 (4 * (index.val - 24))
      ramEncoding before address = (⟨.blakeRound, w⟩ : Delegation.Row p).readWord (wordIndex index) ∧
        ramEncoding after address = (⟨.blakeRound, w⟩ : Delegation.Row p).writtenWord (wordIndex index) := by
  intro index
  have member : importedConstraintsMemoryPorts[wordIndex index] ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports :=
    Array.getElem_mem (wordIndex index).isLt
  exact ⟨ram_encoding_native (reads _ member) (observed index).1,
    ram_encoding_native (writes _ member) (observed index).2⟩

theorem physical_row_words {p : Nat} {w : Nat → ZMod p} {before after : State}
    {statePointer messagePointer : BitVec 32} (round : Fin 10)
    (observed : ∀ index : Fin 40,
      let address := if index.val < 24 then statePointer + BitVec.ofNat 32 (4 * index.val)
        else messagePointer + BitVec.ofNat 32 (4 * (index.val - 24))
      ramEncoding before address = (⟨.blakeRound, w⟩ : Delegation.Row p).readWord (wordIndex index) ∧
        ramEncoding after address = (⟨.blakeRound, w⟩ : Delegation.Row p).writtenWord (wordIndex index)) :
    (Native.input round w).state = (physicalState before statePointer).1 ∧
      (Native.input round w).extended = (physicalState before statePointer).2 ∧
      (Native.input round w).message = blockWords before messagePointer 16 0 ∧
      (Native.output w).state = (physicalState after statePointer).1 ∧
      (Native.output w).extended = (physicalState after statePointer).2 ∧
      blockWords before messagePointer 16 0 = blockWords after messagePointer 16 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Vector.ext
    intro i bound
    change i < 8 at bound
    have result := (observed ⟨i, by omega⟩).1.symm
    interval_cases i
    all_goals simpa [Native.input, physicalState, blockWords, wordIndex,
      Delegation.Row.readWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    have result := (observed ⟨8 + i, by omega⟩).1.symm
    interval_cases i
    all_goals simpa [Native.input, physicalState, blockWords, wordIndex,
      Delegation.Row.readWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    have result := (observed ⟨24 + i, by omega⟩).1.symm
    interval_cases i
    all_goals simpa [Native.input, blockWords, wordIndex,
      Delegation.Row.readWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 8 at bound
    have result := (observed ⟨i, by omega⟩).2.symm
    interval_cases i
    all_goals simpa [Native.output, physicalState, blockWords, wordIndex,
      Delegation.Row.writtenWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    have result := (observed ⟨8 + i, by omega⟩).2.symm
    interval_cases i
    all_goals simpa [Native.output, physicalState, blockWords, wordIndex,
      Delegation.Row.writtenWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    have port : ∀ index : Fin 16,
        (importedConstraintsMemoryPorts[26 + index.val]'(by change 26 + index.val < 43; omega)).writeValue = none := by
      intro index
      fin_cases index <;> rfl
    have same : ((⟨.blakeRound, w⟩ : Delegation.Row p).readWord (wordIndex ⟨24 + i, by omega⟩)) =
        ((⟨.blakeRound, w⟩ : Delegation.Row p).writtenWord (wordIndex ⟨24 + i, by omega⟩)) := by
      simp only [wordIndex, show ¬ 24 + i < 24 by omega, ↓reduceDIte]
      have position : 2 + (24 + i) = 26 + i := by omega
      simp only [position, Delegation.Row.readWord, Delegation.Row.writtenWord, Delegation.Row.ports,
        Delegation.Row.writeToken, readToken, MemoryToken.word, MemoryPort.writeCode, port ⟨i, bound⟩,
        Option.getD_none, MemoryPort.readCode]
    have result := (observed ⟨24 + i, by omega⟩).1.trans
      (same.trans (observed ⟨24 + i, by omega⟩).2.symm)
    simpa [blockWords, show ¬ 24 + i < 24 by omega] using result

end Airbender.Blake2Round.Proofs
