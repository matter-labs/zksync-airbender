import Airbender.Proofs.Blake2G.NativeCall
import Airbender.Proofs.Blake2G.BlockFrame

namespace Airbender.Blake2G.Call.Proofs
open Arithmetic Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem scheduled_counter (reduced : Bool) (i : Nat) :
    (controllerAt reduced i).register.val % 128 <
      if (controllerAt reduced i).register.val / 128 = 0 then 80 else 56 := by
  have bound := Nat.mod_lt i (show 0 < callCount reduced by cases reduced <;> decide)
  cases reduced <;> dsimp [controllerAt, controlAt, callCount] at * <;> split_ifs <;> omega

theorem abi_in_span [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Blake2G.Proofs.BoundaryCallInputs data initial domain reduced)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ data.rows) :
    ∃ register : Fin 256, ABI (nativeArguments register row.assignment).addresses ∧
      (readToken row.assignment importedConstraintsMemoryPorts[8]).word = ⟨register.val, 0⟩ := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨statePointer, messagePointer, stateRead, messageRead, stateAligned, messageAligned, separate, initialized⟩ :=
    Blake2G.Proofs.call_block_domain hp inverse accepted inputs
  obtain ⟨state, message, stateRead', messageRead', pointers, _, _⟩ :=
    Blake2G.Proofs.call_pointers clockBound accepted inputs
  have stateSame := (EStateM.Result.ok.inj (stateRead.symm.trans stateRead')).1
  have messageSame := (EStateM.Result.ok.inj (messageRead.symm.trans messageRead')).1
  subst state
  subst message
  have pointer := pointers row member
  obtain ⟨ordered, permutation, _, controls, _⟩ := Blake2G.Proofs.ordered_controls clockBound accepted inputs
  obtain ⟨i, bound, same⟩ := List.mem_iff_getElem.mp (permutation.mem_iff.mpr member)
  have control := (controls i bound).1
  rw [same] at control
  refine ⟨(controllerAt reduced i).register, ?_, control⟩
  refine ⟨rfl, scheduled_counter reduced i, ?_, ?_, ?_, ?_⟩
  · change (Native.statePointer row.assignment).Bounded ∧ (Native.messagePointer row.assignment).Bounded
    rw [pointer.1, pointer.2]
    exact ⟨Word.ofBitVec_bound _, Word.ofBitVec_bound _⟩
  · change ROM.limit ≤ (Native.statePointer row.assignment).toBitVec.toNat ∧
      ROM.limit ≤ (Native.messagePointer row.assignment).toBitVec.toNat
    rw [pointer.1, pointer.2, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip]
    exact ⟨ram _ (by simpa using initialized true 0), ram _ (by simpa using initialized false 0)⟩
  · change (Native.statePointer row.assignment).toBitVec.toNat % 64 = 0 ∧
      (Native.messagePointer row.assignment).toBitVec.toNat % 64 = 0
    rw [pointer.1, pointer.2, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip]
    exact ⟨stateAligned, messageAligned⟩
  · change (Native.statePointer row.assignment).toBitVec ≠ (Native.messagePointer row.assignment).toBitVec
    rw [pointer.1, pointer.2, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip]
    exact separate

end Airbender.Blake2G.Call.Proofs
