import Airbender.Proofs.Keccak.SplitParityLaneHalves

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- The actual native control and pointer writes have their complete reference words. -/
theorem parity_register_output_words (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable else ColumnParity.clockConstraints columnParityFixedTable))
    (index : Fin 361) (pointer : BitVec 32)
    (next : (parityQueryRow cached w 1)[2] = (bump (controlAt index.val) : ZMod babyBearModulus))
    (pointerWord : (readToken w (parityPointerPort cached)).word = Word.ofBitVec pointer) :
    memoryWord ((parityControlPort cached).writeCode w) = BitVec.ofNat 32 (bump (controlAt index.val)) ∧
      memoryWord ((parityPointerPort cached).writeCode w) = pointer := by
  constructor
  · have small : bump (controlAt index.val) < babyBearModulus :=
      lt_of_lt_of_le (split_control_limb_bounds index).2 (by decide)
    rw [(parity_control_port_codes cached w holds).2, next, ZMod.val_natCast_of_lt small]
    simp only [memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value, mul_zero, add_zero]
  · rw [(parity_pointer_port cached w).2.2]
    change (readToken w (parityPointerPort cached)).word.toBitVec = pointer
    rw [pointerWord, Word.ofBitVec_roundtrip]

/-- The complete native write list has the original reference addresses and values. -/
theorem parity_call_write_projection (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable else ColumnParity.clockConstraints columnParityFixedTable))
    (index : Fin 361) (kind : kindAt index.val = .columnParity)
    (selected : (parityQueryRow cached w 1)[3] = ((paritySelectedRound index).val : ZMod babyBearModulus))
    (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0)
    (pointerWord : (readToken w (parityPointerPort cached)).word = Word.ofBitVec pointer)
    (next : (parityQueryRow cached w 1)[2] = (bump (controlAt index.val) : ZMod babyBearModulus))
    (slots : ∀ lane : Fin 6, (parityQueryRow cached w 0)[1 + lane.val] =
      ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) :
    (((⟨.columnParity, w⟩ : Row babyBearModulus).memorySteps cached).map
      (fun edge => (edge.1.address, edge.2.word.toBitVec))) =
      ((Call.writes index pointer (Call.result index (parityReferenceLanes cached false w))).map
        (fun entry => (entry.1.addressCode, entry.2))) := by
  simp only [Row.memorySteps, List.map_map, Function.comp_def]
  change (((⟨.columnParity, w⟩ : Row babyBearModulus).ports cached).toList.map
    (fun port => (port.address.code w, memoryWord (port.writeCode w)))) = _
  rw [parity_ports_enumeration, parity_native_reference_result cached w holds index kind selected]
  have registerWords := parity_register_output_words cached w holds index pointer next pointerWord
  have controlAddress : (parityControlPort cached).address.code w = (Cell.register 10).addressCode :=
    parity_control_port_address cached w
  have pointerAddress : (parityPointerPort cached).address.code w = (Cell.register 11).addressCode := by
    cases cached <;> rfl
  have address (lane : Fin 6) (high : Bool) :=
    parity_call_lane_address cached high w pointer aligned pointerWord index lane (slots lane)
  have value (lane : Fin 6) (high : Bool) :
      memoryWord ((parityLanePort cached lane high).writeCode w) =
        Call.half (parityReferenceLanes cached true w)[lane.val] high := by
    simpa only [parityReferenceLanes, Vector.getElem_ofFn, dif_pos lane.isLt, ↓reduceIte] using
      (parity_written_port_half cached high w holds lane).symm
  have finList : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide +kernel
  have rangeList : List.range 6 = [0, 1, 2, 3, 4, 5] := by decide +kernel
  simp only [Call.writes, kind, Call.slotCount, finList, rangeList,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_cons, List.map_nil, Nat.reduceLT, ↓reduceDIte,
    controlAddress, pointerAddress, registerWords.1, registerWords.2, address, value]
  rfl

end Airbender.Keccak.Split.Native.Proofs
