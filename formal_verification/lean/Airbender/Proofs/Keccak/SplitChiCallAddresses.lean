import Airbender.Proofs.Keccak.SplitChiCallPointer

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- Every active split lane uses one of the twenty-five physical state slots. -/
theorem split_state_slot_bound (index : Fin 361) (lane : Fin 5) :
    ((Call.slots index)[lane.val]).val < 25 := by
  simp only [Call.slots, Vector.getElem_ofFn, dif_pos lane.isLt]
  exact (Call.physicalSlot _ _).isLt

variable [Fact babyBearModulus.Prime]

/-- Initialized aligned pointer limbs give the original reference RAM address. -/
theorem chi5_call_lane_address (cached high : Bool) (w : Nat → ZMod babyBearModulus)
    (pointer : BitVec 32) (aligned : pointer.toNat % 256 = 0)
    (pointerWord : (readToken w (chi5PointerPort cached)).word = Word.ofBitVec pointer)
    (index : Fin 361) (lane : Fin 5)
    (slot : (chi5ControllerRow cached w)[3 + lane.val] =
      ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) :
    (chi5LanePort cached lane high).address.code w =
      (Call.laneCell pointer (Call.slots index)[lane.val] high).addressCode := by
  have word := (chi5_pointer_word cached w).symm.trans pointerWord
  have low := congrArg Word.lo word
  have upper := congrArg Word.hi word
  change (chi5Pointer cached w)[0].val = pointer.toNat % 65536 at low
  change (chi5Pointer cached w)[1].val = pointer.toNat / 65536 at upper
  have lowCast : (chi5Pointer cached w)[0] = ((pointer.toNat % 65536 : Nat) : ZMod babyBearModulus) := by
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod babyBearModulus)) low
  let physical : Fin 25 := ⟨(Call.slots index)[lane.val].val, split_state_slot_bound index lane⟩
  have room := chi5_pointer_lane_room pointer aligned physical high
  let offset : Nat := 8 * physical.val + if high then 4 else 0
  have bitSum : (pointer + BitVec.ofNat 32 offset).toNat = pointer.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have offsetSmall : offset < 2 ^ 32 := by dsimp [offset]; omega
    have sumSmall : pointer.toNat + offset < 2 ^ 32 := by dsimp [offset]; omega
    simp only [Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt sumSmall]
  have canonical : (pointer.toNat % 65536 + offset : Nat) < babyBearModulus :=
    lt_of_lt_of_le (by simpa only [offset, Nat.add_assoc] using room.1) (by decide)
  rw [chi5_lane_port_address, slot, lowCast, upper]
  have packed :
      (((pointer.toNat % 65536 : Nat) : ZMod babyBearModulus) + 8 *
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus) +
        (if high then 4 else 0 : ZMod babyBearModulus)).val = pointer.toNat % 65536 + offset := by
    have cast : ((pointer.toNat % 65536 + offset : Nat) : ZMod babyBearModulus) =
        ((pointer.toNat % 65536 : Nat) : ZMod babyBearModulus) +
          8 * ((Call.slots index)[lane.val].val : ZMod babyBearModulus) +
          (if high then 4 else 0 : ZMod babyBearModulus) := by
      cases high
      all_goals norm_num [offset, physical, Nat.cast_add, Nat.cast_mul]
      all_goals ring
    rw [← cast]
    exact ZMod.val_natCast_of_lt canonical
  rw [packed]
  change Nat.pair 1 (Nat.pair _ _) = Nat.pair 1 (Nat.pair
    ((pointer + BitVec.ofNat 32 offset).toNat % 65536)
    ((pointer + BitVec.ofNat 32 offset).toNat / 65536))
  rw [bitSum]
  have quotient : (pointer.toNat + offset) / 65536 = pointer.toNat / 65536 := by
    dsimp [offset] at *
    omega
  have remainder : (pointer.toNat + offset) % 65536 = pointer.toNat % 65536 + offset := by
    dsimp [offset] at *
    omega
  rw [quotient, remainder]

end Airbender.Keccak.Split.Native.Proofs
