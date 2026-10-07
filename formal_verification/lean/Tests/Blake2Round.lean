import Airbender.Review.Blake2Round.Theorems
import Airbender.Proofs.Blake2Round.Diagonal

namespace Tests.Blake2Round
open Airbender

/-- Reject a wrong first final-word value through the public claim, with all
    inputs read from the assignment rather than an artificial zero state. -/
theorem wrongFinalWriteRejected (w : Nat → ZMod babyBearModulus)
    (mask : ∀ i : Fin 10, w Blake2Round.Variables.roundBits[i] = if i = 9 then 1 else 0)
    (reduced : w 139 = 0)
    (wrong : (Blake2Round.Preparation.words w Blake2Round.Finalization.stateWrites)[0].value ≠
      (Blake2Round.Preparation.words w Blake2Round.Variables.chainingInputs)[0].value ^^^
      (Blake2Round.Preparation.words w Blake2Round.Mixing.extendedWrites)[0].value ^^^
      (Blake2Round.Preparation.words w Blake2Round.Mixing.extendedWrites)[8].value) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) := by
  intro row
  let input : Blake2Round.Finalization.Input := ⟨9, false,
    Blake2Round.Preparation.words w Blake2Round.Variables.stateReads,
    Blake2Round.Preparation.words w Blake2Round.Variables.chainingInputs,
    Blake2Round.Preparation.words w Blake2Round.Mixing.extendedWrites⟩
  let output := Blake2Round.Preparation.words w Blake2Round.Finalization.stateWrites
  have mapping : Blake2Round.Finalization.WordMapping input output w :=
    ⟨reduced, rfl, rfl, rfl, rfl⟩
  have correct := Blake2Round.Finalization.babyBear_soundness input output w ⟨⟨mask⟩, row, mapping⟩
  simp only [Blake2Round.Finalization.spec, Blake2Round.Finalization.isFinal, input,
    beq_self_eq_true, Bool.true_or, ↓reduceIte] at correct
  have head := congrArg (fun values : Vector Nat 8 => values[0]) correct
  apply wrong
  simpa [input, output, Fin.getElem_fin] using head

/-- The actual finalization query rejects 3 XOR 5 = 7 independently of the mux. -/
theorem wrongFinalChunkRejected (w : Nat → ZMod babyBearModulus) :
    ¬ (FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) ∧
      w 628 = 3 ∧ w 578 = 5 ∧ w 629 = 7) := by
  intro ⟨row, left, right, wrong⟩
  have member := Verification.lookup_of_holds row
    ⟨146, by rw [Blake2Round.lookup_count]; decide⟩
  have correct := Blake2Round.Proofs.xor_lookup_raw (by decide) 3 member
    (by rfl) (by simp [Blake2Round.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment])
  have xor := correct.2.2.2
  simp [Blake2Round.importedConstraints, FlatOperation.lookups, Expression.eval,
    Verification.environment] at xor
  norm_num [left, right, wrong, ZMod.val_ofNat, babyBearModulus] at xor
  exact (by decide : ¬ (7 : Nat) = 3 ^^^ 5) xor

theorem wrongFinalFlagRejected (w : Nat → ZMod babyBearModulus)
    (mask : ∀ i : Fin 10, w Blake2Round.Variables.roundBits[i] = if i = 9 then 1 else 0)
    (reduced : w 139 = 0) (disabled : w 152 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) := by
  intro row
  let input : Blake2Round.Finalization.Input := ⟨9, false,
    Blake2Round.Preparation.words w Blake2Round.Variables.stateReads,
    Blake2Round.Preparation.words w Blake2Round.Variables.chainingInputs,
    Blake2Round.Preparation.words w Blake2Round.Mixing.extendedWrites⟩
  let output := Blake2Round.Preparation.words w Blake2Round.Finalization.stateWrites
  have mapping : Blake2Round.Finalization.WordMapping input output w :=
    ⟨reduced, rfl, rfl, rfl, rfl⟩
  have flag := Blake2Round.Proofs.finalization_flag row mapping mask
  norm_num [input, Blake2Round.Finalization.isFinal, disabled] at flag

theorem wrongNonfinalWriteRejected (w : Nat → ZMod babyBearModulus)
    (mask : ∀ i : Fin 10, w Blake2Round.Variables.roundBits[i] = if i = 0 then 1 else 0) :
    let input : Blake2Round.Finalization.Input := ⟨0, false, Vector.replicate 8 ⟨0, 0⟩,
      Blake2Round.Preparation.words w Blake2Round.Variables.chainingInputs,
      Blake2Round.Preparation.words w Blake2Round.Mixing.extendedWrites⟩
    let output : Blake2Round.Finalization.Output := (Vector.replicate 8 ⟨0, 0⟩).set 0 ⟨1, 0⟩
    ¬ Blake2Round.Finalization.circuitModel.relation input output w := by
  intro input output row
  have interface : Blake2Round.Finalization.NonFinalAssumptions input output w :=
    ⟨⟨mask⟩, by norm_num [input]⟩
  have correct := Blake2Round.Finalization.babyBear_nonfinal_soundness input output w ⟨interface, row⟩
  change output = input.state at correct
  have head := congrArg (fun state : Vector Arithmetic.Word 8 => state[0].lo) correct
  norm_num [input, output] at head

set_option maxRecDepth 16384 in
/-- A zero-input round cannot write one to its first extended-state word.
    This tests the public theorem through the actual imported writeback. -/
theorem wrongRoundOutputRejected (w : Nat → ZMod babyBearModulus) :
    let input : Blake2Round.Mixing.Input :=
      ⟨Vector.replicate 16 ⟨0, 0⟩, Vector.replicate 16 ⟨0, 0⟩⟩
    let output : Blake2Round.Mixing.Output := (Vector.replicate 16 ⟨0, 0⟩).set 0 ⟨1, 0⟩
    ¬ (Blake2Round.Mixing.circuitModel.relation input output w) := by
  intro input output row
  have interface : Blake2Round.Mixing.InterfaceAssumptions input output w := by
    constructor
    · intro i
      norm_num [input, Arithmetic.Word.Bounded, Arithmetic.limbBase]
    · intro i
      norm_num [input, Arithmetic.Word.Bounded, Arithmetic.limbBase]
  have correct := Blake2Round.Mixing.babyBear_soundness input output w ⟨interface, row⟩
  unfold Blake2Round.Mixing.spec at correct
  have head := congrArg (fun state : Vector Nat 16 => state[0]) correct
  rw [Blake2Round.Proofs.round_phases] at head
  norm_num [input, output, Blake2Round.Proofs.referencePhase, Blake2Round.Proofs.referenceCall,
    Blake2Round.Proofs.callConstants, Specs.BLAKE3.roundConstants, Specs.BLAKE3.g,
    Arithmetic.Word.value, Arithmetic.limbBase, add32, rotRight32, Fin.getElem_fin] at head

/-- A malformed carry in any column call is rejected through the checked
    connection to the reusable G fragment. -/
theorem wrongColumnCarryRejected (call : Fin 4) (w : Nat → ZMod babyBearModulus)
    (carry : w (268 + 46 * call.val) = 2) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) := by
  intro holds
  have flag := Blake2G.Proofs.mixing_flags (Blake2Round.Proofs.column_g_holds call holds) 0
  norm_num [Blake2G.Variables.booleanColumns, Blake2Round.Proofs.columnGAssignment,
    Blake2Round.Proofs.columnGBase, Blake2G.Proofs.assemble, carry] at flag
  exact (by decide : ¬ ((2 : ZMod babyBearModulus) = 0 ∨ (2 : ZMod babyBearModulus) = 1)) flag

/-- Each diagonal call is also connected to the native G carry constraints. -/
theorem wrongDiagonalCarryRejected (call : Fin 4) (w : Nat → ZMod babyBearModulus)
    (carry : w (452 + 44 * call.val) = 2) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) := by
  intro holds
  have flag := Blake2G.Proofs.mixing_flags
    (Blake2Round.Proofs.diagonal_g_holds (by decide) call holds) 0
  norm_num [Blake2G.Variables.booleanColumns, Blake2Round.Proofs.diagonalGAssignment,
    Blake2Round.Proofs.diagonalGBase, Blake2G.Proofs.assemble, carry] at flag
  exact (by decide : ¬ ((2 : ZMod babyBearModulus) = 0 ∨ (2 : ZMod babyBearModulus) = 1)) flag

/-- A row whose next round mask does not shift is rejected by the imported
    assertions, independently of which XOR setup is supplied. -/
theorem wrongControlRejected (setup : Table (ZMod babyBearModulus) (fields 4))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (Blake2Round.Control.circuitModel setup).relation ⟨123, 8⟩ ⟨0, 8⟩ w := by
  intro row
  have correct := Blake2Round.Control.babyBear_soundness setup ⟨123, 8⟩ ⟨0, 8⟩ w row
  have high := congrArg Arithmetic.Word.hi correct.2
  norm_num [Blake2Round.Control.next] at high

/-- A wrong XOR output at the actual first G query cannot satisfy the artifact.
    Table provenance and cryptographic lookup enforcement are separate obligations. -/
theorem wrongFirstXorRejected (w : Nat → ZMod babyBearModulus) :
    ¬ (FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) ∧
      w 274 = 3 ∧ w 272 = 5 ∧ w 275 = 7) := by
  intro ⟨row, left, right, wrong⟩
  have member := Verification.lookup_of_holds row
    ⟨2, by rw [Blake2Round.lookup_count]; decide⟩
  have correct := Blake2Round.Proofs.xor_lookup_raw (by decide) 0 member
    (by rfl) (by simp [Blake2Round.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment])
  have xor := correct.2.2.2
  simp [Blake2Round.importedConstraints, FlatOperation.lookups, Expression.eval,
    Verification.environment] at xor
  norm_num [left, right, wrong, ZMod.val_ofNat, babyBearModulus] at xor
  exact (by decide : (7 : Nat) ≠ 3 ^^^ 5) xor

open Blake2Round.Preparation in
/-- The first normal round must take lane zero from the chaining state,
    even when the old extended-state lane has a different value. -/
theorem wrongFirstStateRejected (setup : Table (ZMod babyBearModulus) (fields 4))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints setup) ∧
      w 142 = 1 ∧ w 141 = 0 ∧ w 140 = 0 ∧ w 5 = 10 ∧ w 155 = 20) := by
  intro ⟨row, first, compression, right, stateWord, wrong⟩
  let input : Input := ⟨true, false, false, words w Blake2Round.Variables.stateReads,
    words w Blake2Round.Variables.extendedReads, words w Blake2Round.Variables.messageReads⟩
  let output : Output := ⟨words w Blake2Round.Variables.chainingInputs,
    words w Blake2Round.Variables.preparedState, words w Blake2Round.Variables.preparedMessage⟩
  have correct := babyBear_soundness setup input output w
    ⟨row, ⟨first, compression, right, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have low := congrArg (fun result : Output => result.extended[0].lo) correct
  have selected : (step input).extended[0] = input.state[0] :=
    Vector.getElem_append_left (xs := input.state)
      (ys := (iv.set 4 input.extended[12]).set 6 input.extended[14]) (by decide)
  rw [selected] at low
  norm_num [input, output, words, Blake2Round.Variables.preparedState,
    Blake2Round.Variables.stateReads, stateWord, wrong, babyBearModulus, ZMod.val_ofNat] at low

open Blake2Round.Preparation in
/-- In left-node compression mode the first message word comes from the
    chaining state, not the path data. -/
theorem wrongCompressionOrderRejected (setup : Table (ZMod babyBearModulus) (fields 4))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints setup) ∧
      w 142 = 0 ∧ w 141 = 1 ∧ w 140 = 0 ∧ w 5 = 3 ∧ w 204 = 5) := by
  intro ⟨row, first, compression, right, stateWord, wrong⟩
  let input : Input := ⟨false, true, false, words w Blake2Round.Variables.stateReads,
    words w Blake2Round.Variables.extendedReads, words w Blake2Round.Variables.messageReads⟩
  let output : Output := ⟨words w Blake2Round.Variables.chainingInputs,
    words w Blake2Round.Variables.preparedState, words w Blake2Round.Variables.preparedMessage⟩
  have correct := babyBear_soundness setup input output w
    ⟨row, ⟨first, compression, right, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have low := congrArg (fun result : Output => result.message[0].lo) correct
  have selected : (step input).message[0] = input.state[0] :=
    Vector.getElem_append_left (xs := input.state) (ys := input.message.take 8) (by decide)
  rw [selected] at low
  norm_num [input, output, words, Blake2Round.Variables.preparedMessage,
    Blake2Round.Variables.stateReads, stateWord, wrong, babyBearModulus, ZMod.val_ofNat] at low

open Blake2Round.Schedule in
/-- Round zero's first selected word must equal the prepared first word. -/
theorem wrongPermutationRejected (setup : Table (ZMod babyBearModulus) (fields 4))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints setup) ∧
      (∀ i : Fin 10, w Blake2Round.Variables.roundBits[i] = if i = 0 then 1 else 0) ∧
      w 204 = 3 ∧ w 236 = 5) := by
  intro ⟨row, mask, firstWord, wrong⟩
  let input : Input := ⟨0, Blake2Round.Preparation.words w Blake2Round.Variables.preparedMessage⟩
  let output : Output := Blake2Round.Preparation.words w Blake2Round.Variables.scheduledMessage
  have correct := babyBear_soundness setup input output w ⟨⟨mask⟩, row, ⟨rfl, rfl⟩⟩
  have low := congrArg (fun result : Output => result[0].lo) correct
  norm_num [input, output, step, Blake2Round.Preparation.words,
    Blake2Round.Variables.preparedMessage, Blake2Round.Variables.scheduledMessage,
    Blake2G.Control.messageSchedule, firstWord, wrong, babyBearModulus, ZMod.val_ofNat] at low

end Tests.Blake2Round
