module
public import Proven.Blake2Round.Mask.RVBody
public import Proven.Blake2Round.Mask.RVEffectChoice
public import Proven.Blake2Round.Mask.RVFlags
public import Proven.Blake2Round.Mask.RVSeparate
public import Proven.Blake2Round.Mask.RVCallLink
public import Proven.Blake2Round.Memory

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic Trace Trace.Proofs Delegation.Proofs Blake2Round.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Specs.BLAKE3.g Specs.BLAKE3.round

/-- An initialized native round row executes one actual RV call for every accepted Boolean mask. -/
theorem rv_native_round_call {w : Nat → ZMod babyBearModulus} {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setupTable))
    (reads : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports, (readToken w port).word.Bounded)
    (ports : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w)))
    (distinct : ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map fun edge => edge.1.address).Nodup)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeRound w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) (pc : RV.Word) :
    ∃ next, RV.calls [.blakeRound] (before.setPC pc) = some next ∧ RV.Same next (after.setPC (pc + 4)) := by
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (importedConstraints setupTable) importedConstraintsTimestampLookups)
  have readBounds : ∀ i : Fin 43, (readWord w i).Bounded := by
    intro i
    exact reads importedConstraintsMemoryPorts[i.val] (Array.getElem_mem (by change i.val < 43; exact i.isLt))
  have assumptions := native_assumptions readBounds
  have correct := native_effect core readBounds
  let state := (inputOf w).statePointer.toBitVec
  let message := (inputOf w).messagePointer.toBitVec
  have pointers : (inputOf w).statePointer = Word.ofBitVec state ∧
      (inputOf w).messagePointer = Word.ofBitVec message :=
    ⟨(word_of_toBitVec assumptions.pointers.1).symm, (word_of_toBitVec assumptions.pointers.2).symm⟩
  have address := round_word_address (round := 0) correct.2.2.2 pointers
  have alignment := Blake2Round.Proofs.pointer_alignment (by decide) (by decide) core
  have stateAligned : state.toNat % 128 = 0 := pointer_aligned_128 assumptions.pointers.1 (by
    change (readWord w 0).lo % 128 = 0
    rw [state_pointer]
    exact alignment.1)
  have messageAligned : message.toNat % 64 = 0 := pointer_aligned_64 assumptions.pointers.2 (by
    change (readWord w 25).lo % 64 = 0
    rw [message_pointer]
    exact alignment.2)
  have observed : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w := by
    intro port present
    obtain ⟨cell, code, _⟩ := ports port present
    exact ⟨cell, code⟩
  have separate := native_pointer_separate address observed distinct
  have writes := native_memory_write_rule (by decide) (by decide) holds reads
  have physical := rv_physical_words correct.2.2.2 pointers reads writes ports
  have hRead := congrArg (fun words : Vector Word 8 => words.map Word.toBitVec) physical.1
  simp only [rvPhysicalState] at hRead
  rw [rv_block_words] at hRead
  have eRead := congrArg (fun words : Vector Word 16 => words.map Word.toBitVec) physical.2.1
  simp only [rvPhysicalState] at eRead
  rw [rv_block_words_offset] at eRead
  have mRead := congrArg (fun words : Vector Word 16 => words.map Word.toBitVec) physical.2.2.1
  rw [rv_block_words] at mRead
  have stateWords := congrArg (fun words : Vector Word 8 => words.map Word.toBitVec) physical.2.2.2.1.symm
  have extendedWords := congrArg (fun words : Vector Word 16 => words.map Word.toBitVec) physical.2.2.2.2.1.symm
  obtain ⟨x10, x10'⟩ := rv_register_port (index := 10) 0 rfl ports
  obtain ⟨x11, x11'⟩ := rv_register_port (index := 11) 25 rfl ports
  obtain ⟨x12, x12'⟩ := rv_register_port (index := 12) 42 rfl ports
  have source10 : before.getReg 10 = state := x10
  have source11 : before.getReg 11 = message := x11
  have source12 : before.getReg 12 = (inputOf w).controller.toBitVec := x12
  have effect : RV.Delegation.effect .blakeRound (before.getReg 10) (before.getReg 11) (before.getReg 12) before.mem =
      some (⟨RV.writesAt state ((outputOf w).state.map Word.toBitVec) ++
        RV.writesAt (state + 32) ((outputOf w).extended.map Word.toBitVec), 12,
        (outputOf w).controller.toBitVec⟩ : RV.Effect) := by
    change RV.Delegation.blakeRound (before.getReg 10) (before.getReg 11) (before.getReg 12) before.mem = _
    rw [source10, source11, source12]
    rw [native_round_effect state message _ before.mem stateAligned messageAligned
      (by have := message.isLt; simp only [RV.RAM_END]; omega) separate (native_control_lt core assumptions.controller)]
    exact congrArg some (masked_body before.mem state message assumptions correct hRead eRead mRead
      (native_mask_bits core assumptions.controller) (native_mode_bits core assumptions.controller))
  obtain ⟨regFrame, memFrame⟩ := rv_round_row_frame address observed history permutation aligned
  have fields := rv_history_fields history
  apply two_block_call stateAligned effect stateWords extendedWords x12' _ _ fields.2.1 fields.2.2 pc
  · intro r r12
    by_cases r10 : r = 10
    · subst r10
      exact x10'.trans x10.symm
    by_cases r11 : r = 11
    · subst r11
      exact x11'.trans x11.symm
    exact regFrame r r10 r11 r12
  · intro a alignedA outsideState
    by_cases inMessage : ∃ j : Fin 16, a = message + BitVec.ofNat 32 (4 * j.val)
    · obtain ⟨j, rfl⟩ := inMessage
      have entry := congrArg (fun words : Vector Word 16 => words[j]) physical.2.2.2.2.2
      simp only [rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add, rvRamEncoding] at entry
      have bits := congrArg Word.toBitVec entry
      simpa only [Word.ofBitVec_roundtrip] using bits.symm
    · exact memFrame a alignedA outsideState (fun j same => inMessage ⟨j, same⟩)

end Airbender.Blake2Round.Mask.Proofs
