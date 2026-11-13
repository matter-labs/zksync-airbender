module
public import Proven.Blake2G.NativeFields

@[expose] public section
namespace Airbender.Blake2G.Proofs
set_option warningAsError true
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Specs.BLAKE3.g

/-- A native G row executes one RV call from its actual history cut.
    The control byte and both pointers come from the native ports. -/
theorem rv_native_g_call {w : Nat → ZMod babyBearModulus} {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (clockConstraints (setupTable Control.controllerRows)))
    (active : w Variables.execute = 1)
    (reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).ports, (readToken w port).word.Bounded)
    (ports : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w)))
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeG w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) (pc : RV.Word) :
    ∃ next, RV.calls [.blakeG] (before.setPC pc) = some next ∧ RV.Same next (after.setPC (pc + 4)) := by
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Control.controllerRows)) importedConstraintsTimestampLookups)
  have controlRead := reads importedConstraintsMemoryPorts[8] (Array.getElem_mem (by change 8 < 9; decide))
  have low : (w Variables.controlReadLo).val < 65536 := by
    simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
      importedConstraintsMemoryPorts, limbBase] using controlRead.1
  have byte := native_control_bound core active low
  let register : Fin 256 := ⟨(w Variables.controlReadLo).val, byte⟩
  let stateWord := Native.statePointer w
  let messageWord := Native.messagePointer w
  let state := stateWord.toBitVec
  let message := messageWord.toBitVec
  have stateBound : stateWord.Bounded := reads importedConstraintsMemoryPorts[0] (Array.getElem_mem (by change 0 < 9; decide))
  have messageBound : messageWord.Bounded := reads importedConstraintsMemoryPorts[5] (Array.getElem_mem (by change 5 < 9; decide))
  have alignment := pointer_alignment (by decide) (by decide) core
  have stateAligned : state.toNat % 64 = 0 := native_pointer_aligned stateBound (by
    simpa [stateWord, Native.statePointer, Delegation.Row.readWord, Delegation.Row.ports, readToken,
      MemoryToken.word, MemoryPort.readCode, WordColumns.code, importedConstraintsMemoryPorts] using alignment.1)
  have messageAligned : message.toNat % 64 = 0 := native_pointer_aligned messageBound (by
    simpa [messageWord, Native.messagePointer, Delegation.Row.readWord, Delegation.Row.ports, readToken,
      MemoryToken.word, MemoryPort.readCode, WordColumns.code, importedConstraintsMemoryPorts] using alignment.2)
  have addresses := native_addresses (by decide) (by decide) core active byte reads
  have fixed : addressInput w byte = ⟨⟨register, true⟩, Word.ofBitVec state, Word.ofBitVec message⟩ := by
    simp only [addressInput, state, message, stateWord, messageWord, register]
    rw [word_of_toBitVec stateBound, word_of_toBitVec messageBound]
  rw [fixed] at addresses
  have writes := memory_write_rule (by decide) (by decide) holds reads
  have stateResult := rv_physical_state_result (by decide) (by decide) core active byte addresses reads
    writes ports stateAligned messageAligned history permutation aligned
  obtain ⟨regFrame, memFrame⟩ := rv_g_row_frame addresses
    (fun port present => by obtain ⟨cell, code, _⟩ := ports port present; exact ⟨cell, code⟩)
    history permutation aligned
  obtain ⟨x10, x10'⟩ := rv_native_register_port (index := 10) 0 rfl ports
  obtain ⟨x11, x11'⟩ := rv_native_register_port (index := 11) 5 rfl ports
  obtain ⟨x12, x12'⟩ := rv_native_register_port (index := 12) 8 rfl ports
  have x12Value : memoryWord (importedConstraintsMemoryPorts[8].readCode w) = BitVec.ofNat 32 register.val := by
    have high := (control_high_zero core).1
    change w 4 = 0 at high
    simp [memoryWord, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code,
      register, Variables.controlReadLo, high, Word.toBitVec, Word.value]
  let controlOutput : Control.Output := ⟨⟨(w 5).val, (w 6).val⟩,
    Variables.stateOffsetColumns.map (fun column => (w column).val),
    Variables.messageOffsetColumns.map (fun column => (w column).val)⟩
  have controller : controlOutput = Control.step ⟨register, true⟩ :=
    Control.Proofs.soundness (by decide) _ _ w ⟨core, rfl, active, rfl⟩
  have x12Next : memoryWord (importedConstraintsMemoryPorts[8].writeCode w) =
      (Control.step ⟨register, true⟩).register.toBitVec := by
    have value := congrArg (fun output : Control.Output => output.register.toBitVec) controller
    simpa [controlOutput, memoryWord, importedConstraintsMemoryPorts, MemoryPort.writeCode, WordColumns.code,
      Word.toBitVec, Word.value, limbBase] using value
  have fields := rv_history_fields history
  apply native_g_call_link stateAligned messageAligned stateResult x10 x11 (x12.trans x12Value)
    (x12'.trans x12Next) _ _ fields.2.1 fields.2.2 pc
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
    · obtain ⟨j, same⟩ := inMessage
      have separate : state ≠ message := by
        intro equal
        exact outsideState j (by rw [equal]; exact same)
      have unchanged := rv_native_block_frame ⟨register, true⟩ addresses stateAligned messageAligned separate
        history permutation aligned false j (fun impossible => by cases impossible)
      have words := congrArg Word.toBitVec unchanged
      simpa only [same, Bool.false_eq_true, ↓reduceIte, rvRamEncoding, Word.ofBitVec_roundtrip] using words
    · exact memFrame a alignedA outsideState (fun j same => inMessage ⟨j, same⟩)

end Airbender.Blake2G.Proofs
