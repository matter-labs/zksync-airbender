import Airbender.Proofs.Keccak.SplitChiRegisters

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- Every blessed control transition fits in one native sixteen-bit limb. -/
theorem split_control_limb_bounds : ∀ index : Fin 361,
    controlAt index.val < 65536 ∧ bump (controlAt index.val) < 65536 := by
  decide +kernel

variable [Fact babyBearModulus.Prime]

/-- An active native chi5 row has the blessed control, addresses and lane effect. -/
theorem chi5_native_memory_effect (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (active : w 0 = 1) :
    ∃ index : Fin 361, kindAt index.val = .chi5 ∧
      (chi5ControlPort cached).readCode w = Nat.pair (controlAt index.val) 0 ∧
      (chi5ControlPort cached).writeCode w = Nat.pair (bump (controlAt index.val)) 0 ∧
      (∀ (lane : Fin 5) (high : Bool), (chi5LanePort cached lane high).address.code w =
        Nat.pair 1 (Nat.pair
          ((chi5Pointer cached w)[0] + 8 * ((Call.slots index)[lane.val].val : ZMod babyBearModulus) +
            (if high then 4 else 0 : ZMod babyBearModulus)).val (chi5Pointer cached w)[1].val)) ∧
      (∀ lane : Fin 5, chi5LaneValue cached true w lane = chi5LaneValue cached false w lane ^^^
        (not64 (chi5LaneValue cached false w ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) &&&
          chi5LaneValue cached false w ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩)) := by
  obtain ⟨index, kind, before, after, slots, _⟩ := chi5_native_controller_schedule cached w holds active
  have codes := chi5_control_port_codes cached w holds
  have bounds := split_control_limb_bounds index
  have smallBefore : controlAt index.val < babyBearModulus :=
    lt_of_lt_of_le bounds.1 (by decide)
  have smallAfter : bump (controlAt index.val) < babyBearModulus :=
    lt_of_lt_of_le bounds.2 (by decide)
  refine ⟨index, kind, ?_, ?_, ?_, ?_⟩
  · rw [codes.1, before, ZMod.val_natCast_of_lt smallBefore]
  · rw [codes.2, after, ZMod.val_natCast_of_lt smallAfter]
  · intro lane high
    rw [chi5_lane_port_address, slots lane]
  · exact chi5_native_lane_operation cached w holds

end Airbender.Keccak.Split.Native.Proofs
