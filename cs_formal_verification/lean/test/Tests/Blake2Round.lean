module
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Human.Trace.Workers.Keccak.Permutation
public import Slop.Blake2Round.Compression
public import Slop.Blake2Round.StateTransport
public import Slop.Delegation.NativeSegments
public import Slop.Delegation.ReverseFold
public import Slop.Blake2Round.Diagonal
public import Slop.Blake2Round.Finalization
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Circuits.Blake2Round.Artifact
public import Slop.Defs.Circuits.Blake2Round.Preparation
public import Slop.Defs.Circuits.Blake2Round.Mixing
public import Slop.Defs.Circuits.Blake2Round.Finalization

@[expose] public section

namespace Tests.Blake2Round
open Airbender

/-- Highest aligned ABI blocks, using the actual last state/message descriptors. -/
theorem lastStateAddress : (Blake2Round.importedConstraintsIndirectPorts[23]).address
    (fun column => if column = 3 then (65408 : ZMod babyBearModulus)
      else if column = 4 then 65535 else 0) = (0xffffffdc : BitVec 32) := by decide

theorem lastMessageAddress : (Blake2Round.importedConstraintsIndirectPorts[39]).address
    (fun column => if column = 101 then (65472 : ZMod babyBearModulus)
      else if column = 102 then 65535 else 0) = (0xfffffffc : BitVec 32) := by decide

/-- The actual finalization query rejects 3 XOR 5 = 7 independently of the mux. -/
theorem wrongFinalChunkRejected (w : Nat → ZMod babyBearModulus) :
    ¬ (FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) ∧
      w 536 = 3 ∧ w 502 = 5 ∧ w 537 = 7) := by
  intro ⟨row, left, right, wrong⟩
  have member := Verification.lookup_of_holds row
    ⟨130, by rw [Blake2Round.lookup_count]; decide⟩
  have correct := Blake2Round.Proofs.lookup_facts_raw (t := 19) (by decide) member (by rfl)
    (by decide) (by simp [Blake2Round.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment])
  have xor := correct.2.2.1
  simp [Blake2Round.importedConstraints, FlatOperation.lookups, Expression.eval,
    Verification.environment] at xor
  norm_num [left, right, wrong, ZMod.val_ofNat, babyBearModulus] at xor

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

set_option maxRecDepth 16384 in

/-- A malformed carry in any column call is rejected by its imported Boolean assertion. -/
theorem wrongColumnCarryRejected (call : Fin 4) (w : Nat → ZMod babyBearModulus)
    (carry : w (268 + 40 * call.val) = 2) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) := by
  intro holds
  have flag := Verification.assertion_of_holds holds
    ⟨137 + 4 * call.val, by rw [Blake2Round.constraint_count]; omega⟩
  fin_cases call
  all_goals op_index at flag
  all_goals eval_entry at flag
  all_goals norm_num at carry
  all_goals rw [carry] at flag
  all_goals exact absurd flag (by decide)

/-- Each diagonal call's first carry is rejected by its imported Boolean assertion. -/
theorem wrongDiagonalCarryRejected (call : Fin 4) (w : Nat → ZMod babyBearModulus)
    (carry : w (426 + 30 * call.val) = 2) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) := by
  intro holds
  have flag := Verification.assertion_of_holds holds
    ⟨153 + 2 * call.val, by rw [Blake2Round.constraint_count]; omega⟩
  fin_cases call
  all_goals op_index at flag
  all_goals eval_entry at flag
  all_goals norm_num at carry
  all_goals rw [carry] at flag
  all_goals exact absurd flag (by decide)

/-- A wrong XOR output at the actual first G query (byte XOR with carry) cannot
    satisfy the artifact. -/
theorem wrongFirstXorRejected (w : Nat → ZMod babyBearModulus) :
    ¬ (FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) ∧
      w 260 = 3 ∧ w 256 = 5 ∧ w 262 = 7) := by
  intro ⟨row, left, right, wrong⟩
  have member := Verification.lookup_of_holds row
    ⟨2, by rw [Blake2Round.lookup_count]; decide⟩
  have correct := Blake2Round.Proofs.lookup_facts_raw (t := 55) (by decide) member (by rfl)
    (by decide) (by simp [Blake2Round.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment])
  have xor := correct.2.2.2.1
  simp [Blake2Round.importedConstraints, FlatOperation.lookups, Expression.eval,
    Verification.environment] at xor
  norm_num [left, right, wrong, ZMod.val_ofNat, babyBearModulus] at xor

end Tests.Blake2Round
