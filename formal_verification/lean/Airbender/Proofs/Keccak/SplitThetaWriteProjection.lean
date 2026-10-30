import Airbender.Proofs.Keccak.SplitThetaLaneHalves

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The actual native control and pointer writes have their complete reference words. -/
theorem theta_register_output_words (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable else ThetaRho.clockConstraints thetaRhoFixedTable))
    (index : Fin 361) (pointer : BitVec 32)
    (next : (thetaQueryRow cached w 9)[2] = (bump (controlAt index.val) : ZMod babyBearModulus))
    (pointerWord : (readToken w (thetaPointerPort cached)).word = Word.ofBitVec pointer) :
    memoryWord ((thetaControlPort cached).writeCode w) = BitVec.ofNat 32 (bump (controlAt index.val)) ∧
      memoryWord ((thetaPointerPort cached).writeCode w) = pointer := by
  constructor
  · have small : bump (controlAt index.val) < babyBearModulus :=
      lt_of_lt_of_le (split_control_limb_bounds index).2 (by decide)
    rw [(theta_control_port_codes cached w holds).2, next, ZMod.val_natCast_of_lt small]
    simp only [memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value, mul_zero, add_zero]
  · rw [(theta_pointer_port cached w).2.2]
    change (readToken w (thetaPointerPort cached)).word.toBitVec = pointer
    rw [pointerWord, Word.ofBitVec_roundtrip]

/-- The complete native write list has the original reference addresses and values. -/
theorem theta_call_write_projection (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable else ThetaRho.clockConstraints thetaRhoFixedTable))
    (index : Fin 361) (kind : kindAt index.val = .thetaRho)
    (selected : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = index.val % 5 then 1 else 0)
    (bounded : ∀ (lane : Fin 7) (high : Bool), (readToken w (thetaLanePort cached lane high)).word.Bounded)
    (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0)
    (pointerWord : (readToken w (thetaPointerPort cached)).word = Word.ofBitVec pointer)
    (next : (thetaQueryRow cached w 9)[2] = (bump (controlAt index.val) : ZMod babyBearModulus))
    (slots : ∀ lane : Fin 7, (thetaQueryRow cached w 0)[1 + lane.val] =
      ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) :
    (((⟨.thetaRho, w⟩ : Row babyBearModulus).memorySteps cached).map
      (fun edge => (edge.1.address, edge.2.word.toBitVec))) =
      ((Call.writes index pointer (Call.result index (thetaReferenceLanes cached false w))).map
        (fun entry => (entry.1.addressCode, entry.2))) := by
  simp only [Row.memorySteps, List.map_map, Function.comp_def]
  change (((⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached).toList.map
    (fun port => (port.address.code w, memoryWord (port.writeCode w)))) = _
  rw [theta_ports_enumeration, theta_native_reference_result cached w holds index kind selected
    (theta_read_limb_bounds cached w 6 (bounded 6))]
  have registerWords := theta_register_output_words cached w holds index pointer next pointerWord
  have controlAddress : (thetaControlPort cached).address.code w = (Cell.register 10).addressCode :=
    theta_control_port_address cached w
  have pointerAddress : (thetaPointerPort cached).address.code w = (Cell.register 11).addressCode := by
    cases cached <;> rfl
  have address (lane : Fin 7) (high : Bool) :=
    theta_call_lane_address cached high w pointer aligned pointerWord index lane (slots lane)
  have value (lane : Fin 7) (high : Bool) :
      memoryWord ((thetaLanePort cached lane high).writeCode w) =
        Call.half (thetaReferenceLanes cached true w)[lane.val] high := by
    simpa only [thetaReferenceLanes, Vector.getElem_ofFn] using
      (theta_written_port_half cached high w holds
        ⟨index.val % 5, Nat.mod_lt _ (by decide)⟩ selected bounded lane).symm
  have finList : List.finRange 7 = [0, 1, 2, 3, 4, 5, 6] := by decide +kernel
  have rangeList : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := by decide +kernel
  simp only [Call.writes, kind, Call.slotCount, finList, rangeList,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_cons, List.map_nil, Nat.reduceLT, ↓reduceDIte,
    controlAddress, pointerAddress, registerWords.1, registerWords.2, address, value]
  rfl

end Airbender.Keccak.Split.Native.Proofs
