import Airbender.Proofs.Keccak.SplitChiLaneHalves

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- The actual native control and pointer writes have their complete reference words. -/
theorem chi5_register_output_words (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (index : Fin 361) (pointer : BitVec 32)
    (next : (chi5ControllerRow cached w)[2] = (bump (controlAt index.val) : ZMod babyBearModulus))
    (pointerWord : (readToken w (chi5PointerPort cached)).word = Word.ofBitVec pointer) :
    memoryWord ((chi5ControlPort cached).writeCode w) = BitVec.ofNat 32 (bump (controlAt index.val)) ∧
      memoryWord ((chi5PointerPort cached).writeCode w) = pointer := by
  constructor
  · have small : bump (controlAt index.val) < babyBearModulus :=
      lt_of_lt_of_le (split_control_limb_bounds index).2 (by decide)
    rw [(chi5_control_port_codes cached w holds).2, next, ZMod.val_natCast_of_lt small]
    simp only [memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value, mul_zero, add_zero]
  · rw [(chi5_pointer_port cached w).2.2]
    change (readToken w (chi5PointerPort cached)).word.toBitVec = pointer
    rw [pointerWord, Word.ofBitVec_roundtrip]

/-- The complete native write list has the original reference addresses and values. -/
theorem chi5_call_write_projection (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (index : Fin 361) (kind : kindAt index.val = .chi5) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0)
    (pointerWord : (readToken w (chi5PointerPort cached)).word = Word.ofBitVec pointer)
    (next : (chi5ControllerRow cached w)[2] = (bump (controlAt index.val) : ZMod babyBearModulus))
    (slots : ∀ lane : Fin 5, (chi5ControllerRow cached w)[3 + lane.val] =
      ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) :
    (((⟨.chi5, w⟩ : Row babyBearModulus).memorySteps cached).map
      (fun edge => (edge.1.address, edge.2.word.toBitVec))) =
      ((Call.writes index pointer (Call.result index (chi5ReferenceLanes cached false w))).map
        (fun entry => (entry.1.addressCode, entry.2))) := by
  simp only [Row.memorySteps, List.map_map, Function.comp_def]
  change (((⟨.chi5, w⟩ : Row babyBearModulus).ports cached).toList.map
    (fun port => (port.address.code w, memoryWord (port.writeCode w)))) = _
  rw [chi5_ports_enumeration, chi5_native_reference_result cached w holds index kind]
  have registerWords := chi5_register_output_words cached w holds index pointer next pointerWord
  have controlAddress : (chi5ControlPort cached).address.code w = (Cell.register 10).addressCode :=
    chi5_control_port_address cached w
  have pointerAddress : (chi5PointerPort cached).address.code w = (Cell.register 11).addressCode := by
    cases cached <;> rfl
  have address (lane : Fin 5) (high : Bool) :=
    chi5_call_lane_address cached high w pointer aligned pointerWord index lane (slots lane)
  have value (lane : Fin 5) (high : Bool) :
      memoryWord ((chi5LanePort cached lane high).writeCode w) =
        Call.half (chi5ReferenceLanes cached true w)[lane.val] high := by
    simpa only [chi5ReferenceLanes, Vector.getElem_ofFn, dif_pos lane.isLt, ↓reduceIte] using
      (chi5_lane_port_half cached true high w holds lane).symm
  have finList : List.finRange 5 = [0, 1, 2, 3, 4] := by decide +kernel
  have rangeList : List.range 5 = [0, 1, 2, 3, 4] := by decide +kernel
  simp only [Call.writes, kind, Call.slotCount, finList, rangeList,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_cons, List.map_nil, Nat.reduceLT, ↓reduceDIte,
    controlAddress, pointerAddress, registerWords.1, registerWords.2, address, value]
  rfl

end Airbender.Keccak.Split.Native.Proofs
